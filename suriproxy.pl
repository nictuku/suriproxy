#!/usr/bin/perl -W

# Suriproxy Copyright 2004, Yves Junqueira <yves.junqueira at gmail.com>
# uribl Copyright 2004, Devin Carrway <qpsmtpd@devin.com>
# smtpproxy Copyright notices below
use Mail::SpamAssassin;
use Digest::MD5 qw(md5_hex);
use Net::Server::Daemonize qw(daemonize);
use Unix::Syslog qw(:macros);
use Unix::Syslog qw(:subs);
use strict;
use Getopt::Long;
use IO::File;

use lib '.';
use MSDW::SMTP::Server;
use MSDW::SMTP::Client;
use Net::DNS::Resolver;

############################################################
# Options

my %uribl_options = (
    'surblgoiano.com.br' => '',
    'multi.surbl.org'    => '',
);

# If the uribl zone is md5-enabled, the MD5 hash of the host will be 
# added to the end of this url
# my $refer_url = 'http://something/cgi-bin/grr.cgi?url=';
my $refer_url = 'http://www.surbl.org';

# leading dots whitelists sub domains
my @wl_domains_acl = qw( pop.com.br .microsoft.com hotmail.com kit.net .w3.org
  .lynx.com.br .govesa.com.br med.br);
my @wl_recipients_acl = qw ( postmaster@ abuse@ spambox@);
my $action            = "deny";
my $verbose_level     = 4;
my $check_timeout     = 30;
my $child_timeout     = 3600;
my $mode              = "transparent";
my $deny_code         = "554";
my $deny_msg          = "Content banned - Conteudo banido";
my $daemonize         = 0;
my $dns_timeout       = 5;

# daemon configs.
my $user    = "nobody";
my $group   = "nobody";
my $pidfile = "/var/run/suriproxy.pid";
############################################################
#todo
my $version = '0.11';
my %sockets;
my %checked;
my $tlds =
'zw|zm|za|yu|yt|ye|ws|wf|vu|vn|vi|vg|ve|vc|va|uz|uy|us|um|uk|ug|ua|tz|tw|tv|tt|tr|tp|to|tn|tm|tk|tj|th|tg|tf|td|tc|sz|sy|sv|su|st|sr|so|sn|sm|sl|sk|sj|si|sh|sg|se|sd|sc|sb|sa|rw|ru|ro|re|qa|py|pw|pt|ps|pro|pr|pn|pm|pl|pk|ph|pg|pf|pe|pa|org|om|nz|nu|nr|np|no|nl|ni|ng|nf|net|ne|nc|name|na|mz|my|mx|mw|mv|museum|mu|mt|ms|mr|mq|mp|mo|mn|mm|ml|mk|mil|mh|mg|md|mc|ma|ly|lv|lu|lt|ls|lr|lk|li|lc|lb|la|kz|ky|kw|kr|kn|km|ki|kh|kg|ke|jp|jo|jm|je|it|is|ir|iq|io|int|info|in|im|il|ie|id|hu|ht|hr|hn|hm|hk|gy|gw|gu|gt|gs|gr|gq|gp|gov|gn|gm|gl|gi|gh|gg|gf|ge|gd|gb|ga|fr|fo|fm|fk|fj|fi|et|es|er|eg|ee|edu|ec|dz|do|dm|dk|dj|de|cz|cy|cx|cv|cu|cr|coop|com|co|cn|cm|cl|ck|ci|ch|cg|cf|cd|cc|ca|bz|by|bw|bv|bt|bs|br|bo|bn|bm|bj|biz|bi|bh|bg|bf|be|bd|bb|ba|az|aw|au|at|as|arpa|ar|aq|ao|an|am|al|ai|ag|af|aero|ae|ad|ac';

# reversed so that .com matches before .co
my $refer_msg;
my $server;
my $res = new Net::DNS::Resolver;
$res->udp_timeout($dns_timeout);

# Check SA version
my $SA3 = -1;
if ( $Mail::SpamAssassin::VERSION < 2.6 ) {

    argh(   "Minimum Mail::SpamAssassin version is 2.6. You have"
          . "$Mail::SpamAssassin::VERSION" );
}
elsif ( $Mail::SpamAssassin::VERSION < 3.0 ) {
    do_log( 1, "Found SpamAssassin < 3.0" );
    $SA3 = 0;
}
else {
    do_log( 1, "Found SpamAssassin >= 3.0" );
    $SA3 = 1;
}

my $spamtest = Mail::SpamAssassin->new(
    {
        config_text => "use_bayes          0\n"
          . "skip_rbl_checks    1\n"
          . "bayes_path         /dev/null\n",
        local_tests_only => 1
    }
  )
  or die "Can't create SpamAssassin object";

# from GetURI:
# Remove empty/unclickable anchor tags (poisoning attempts)
# Drastically shortens output :-)
sub remove_empty_anchors($) {
    my $mail = shift;

    $mail =~ s/<[\s\=]*A[\=\s]+([^>]+)>[\s\=]*<[\=\s]*\/[\=\s]*A[\=\s]*>/[]/igs;

    return $mail;
}

sub do_log {
    my ( $pri, $msg ) = @_;
    if ( $verbose_level >= $pri ) {
        openlog "suriproxy", LOG_PID, LOG_MAIL;
        syslog LOG_INFO, "%s", $msg;
        closelog;
    }
}

sub argh {
    my ($die_msg) = defined(@_) ? @_ : '--';
    do_log( 1, "FATAL ERROR: $die_msg" );
    die "FATAL ERROR: $die_msg";
}

sub suri {
    $refer_msg = '';
    undef %checked;
    if ( defined(@_) ) {
        my ($fh) = @_;

        my (
            $dev,  $ino,   $mode,  $nlink,  $uid,     $gid, $rdev,
            $size, $atime, $mtime, $ctime,, $blksize, $blocks
          )
          = $fh->stat
          or do_log( 1, "Error: Can't check mail file: $!" )
          and return 'FAIL';

        # local ( *_, $/ );
        my $from = $server->{from};
        $from =~ s/ \w+=.*//g;

        $fh->seek( 0, 0 ) or do_log(
            1, "Error: Can't rewind message file: 
$!"
          )
          and return 'FAIL';

        do_log( 2, "Checking from=$from, to=@{$server->{to}}, SIZE=$size." );
        do_log( 6, "# of rcpts: " . @{ $server->{to} } . "." );
        my @rcpts = @{ $server->{to} };
        for (@rcpts) {
            s/[<>]//g;
            if ( lookup_acl( $_, \@wl_recipients_acl, 0 ) ) {
                do_log( 3, "Accepting message: $_ is in the whitelist" );
                return 'WHITERCPT';
            }
        }

        $SIG{ALRM} = \&timed_out_check;

        my $ret = eval {
            alarm($check_timeout);

            # test loop
            #while (1) { }

            my @message;
            while (<$fh>) {

                push @message, $_;
            }
            process_msg(@message);
            my %matches;
            while ( keys %sockets ) {
                my $c = 0;
                for my $s ( keys %sockets ) {
#              do_log(2, ".. $s");
                    unless ( $sockets{$s} ) {
                        delete $sockets{$s};
                        next;
                    }
                    next unless $res->bgisready( $sockets{$s} );
                    my $packet = $res->bgread( $sockets{$s} );
                    unless ($packet) {
                        delete $sockets{$s};
                        next;
                    }
                    for my $rr ( $packet->answer ) {
                        $matches{$s} = $rr->txtdata
                          if $rr->type eq 'TXT';
                    }
                    delete $sockets{$s};
                    $c++;
                }
                sleep 0.1 if keys %sockets and !$c;
            }
            for ( keys %matches ) {
                my ( $host, $uribl ) = split /\t/, $_;
                my $note =
"BADURI: from=$from, to=@{$server->{to}} $host in $uribl ($matches{$_}). Action=$action";
                do_log( 3, "$note." );

                if ( $action eq 'deny' ) {
                    $refer_msg =
                        $uribl_options{$uribl} =~ /m/
                      ? $refer_url . $host
                      : $refer_url;
                    return ("DENY $note $refer_msg");

                    #die "nao pode morrer";

                    #close(FILE);
                }
                else { return ("WARN $note"); }

            }

            alarm(0);
            return "OK";
        };
        alarm(0);

        if ( $@ =~ /imeout/ ) {
            return "TIMEOUT";
        }
        if ($ret) { return "$ret"; }
    }
    else {

        return "EMPTY";
    }
    return "ARGH";
}

sub process_msg(@) {
    my $mail;

    if ($SA3) {
        $mail = $spamtest->parse( \@_, 0 ) or argh("235: $!");
        my $text = $spamtest->remove_spamassassin_markup($mail)
          or argh("231: $!");
        $mail->finish();    #	 or argh("211: $!");
        $text = remove_empty_anchors($text) or argh("122: $!");
        $mail = $spamtest->parse($text)     or argh(
            "ERROR 231: Could not 
parse with SA: $!"
        );
    }
    else {
        $mail = Mail::SpamAssassin::NoMailAudit->new( data => \@_ );
        my $text    = $spamtest->remove_spamassassin_markup($mail);
        my @message = split( /$/m, remove_empty_anchors($text) );

        #$mail->delete_metadata();
        $mail = Mail::SpamAssassin::NoMailAudit->new( data => \@message );
    }

    my $status = $spamtest->check($mail);
    my @uris   = Mail::SpamAssassin::PerMsgStatus::get_uri_list($status);
    my ( $display_uri, $check_uri );

    if (@uris) { do_log( 3, "INFO: Found @uris" ); }
    foreach my $uri_text (@uris) {
        $uri_text =~ s/www\.//i;
        if (
            $uri_text =~ m{
                        \w{3,16}:/+                     # protocol
                        (?:\S+@)?                       # user/pass
                        (\d{7,})                        # raw-numeric IP
                        (?::\d+)?([/?\s]|$)             # port, slash
                                                        #  or EOL
                        }gx    # raw-numeric
          )
        {
            my @octets = (
                ( ( $1 >> 24 ) & 0xff ),
                ( ( $1 >> 16 ) & 0xff ),
                ( ( $1 >> 8 ) & 0xff ),
                ( $1 & 0xff )
            );
            $display_uri = join( '.', @octets );
            $check_uri   = join( '.', reverse @octets );
        }
        elsif (
            $uri_text =~ m{
                        \w{3,16}:/+                     # protocol
                        (?:\S+@)?                       # user/pass
                        (\d+|0[xX][0-9A-Fa-f]+)\.       # IP address
                        (\d+|0[xX][0-9A-Fa-f]+)\.
                        (\d+|0[xX][0-9A-Fa-f]+)\.
                        (\d+|0[xX][0-9A-Fa-f]+)
                        }gx
          )
        {
            my @octets = ( $1, $2, $3, $4 );

            # return any octal/hex octets in the IP addr back
            # to decimal form (e.g. http://0x7f.0.0.00001)
            for ( 0 .. $#octets ) {
                $octets[$_] =~ s/^0([0-7]+)$/oct($1)/e;
                $octets[$_] =~ s/^0x([0-9a-fA-F]+)$/hex($1)/e;
            }
            $display_uri = join( '.', @octets );
            $check_uri   = join( '.', reverse @octets );
        }
        elsif (
            $uri_text =~ m{
                        \w{3,16}:/+                     # protocol
                        (?:\S+@)?                       # user/pass
                        ([\w\-.]+\.(${tlds}))[\W]*    # hostname
                        }gx
          )
        {

            $display_uri = $1;
            $check_uri   = $1;
        }
        elsif (
            $uri_text =~ m{
                        mailto:[^@]*@                     # protocol
                        ([\w\-.]+\.(${tlds}))[\W]*    # hostname
                        }gx
          )
        {

            $display_uri = $1;
            $check_uri   = $1;
        }
        elsif ( $uri_text =~ m{([\w\-.]+\.(${tlds}))[\W]*}gx ) {
            $display_uri = $1;
            $check_uri   = $1;
        }

        if ($display_uri) {
            if ( $check_uri eq $display_uri ) {    # hostname
                my @host_domains = split /\./, $check_uri;
                while ( @host_domains >= 2 ) {
                    my $subhost = join( '.', @host_domains );
#         do_log(2,"Teste3 $subhost");
                    check_dns_host($subhost);
                    shift @host_domains;

                }
            }
            else {
           do_log(2, "Teste2 $check_uri");
  check_dns_host($check_uri) }
        }
    }
}

sub check_dns_host($) {

    my ($subhost) = @_;
#    do_log( 5, "Should I check $subhost?" );

        if (   !( $checked{"$subhost"} ) &&
      (!lookup_acl( $subhost, \@wl_domains_acl, 1 ) ) 
 )
        {
    do_log( 5, "Checking address: $subhost" );
    for my $z ( keys %uribl_options ) {
        if ( $uribl_options{$z} =~ /m/ ) {
            $subhost = md5_hex($subhost);
        }
            $sockets{"$subhost\t$z"} = $res->bgsend( "$subhost.$z.", 'txt' );
            $checked{"$subhost"}++;

        }
    }

}

sub timed_out_check {
    do_log( 1, "Error: timeout while checking message\n" );
    argh("Error: Timeout");
}

# Modified version of amavisd-new's
sub split_address($) {
    my ($mailbox) = @_;
    $mailbox =~ /^ (.*?) ( \@ (?:  \[  (?: \\. | [^\]\\] )*  \]
                                 |  [^@"<>\[\]\\\s] )*
                       ) \z/xs ? ( $1, $2 ) : ( $mailbox, '' );
}

# Modified version of amavisd-new's
sub lookup_acl($$$) {
    my ( $addr, $acl_ref, $mode ) = @_;

    #mode 1 = domain only
    #mode 0 = email

    ( ref($acl_ref) eq 'ARRAY' )
      or argh("lookup_acl: arg2 must be a list ref: $acl_ref");
    return undef if !@$acl_ref;    # empty list can't match anything
    my ( $localpart, $domain ) =
      ( $mode == 0 ) ? split_address($addr) : ( undef, $addr );
    $domain    = lc($domain);
    $localpart = lc($localpart);
    local ( $1, $2 );

    # chop off leading @ and trailing dots
    $domain = $1 if $domain =~ /^\@?(.*?)\.*\z/s;
    my ($lcaddr) = $localpart . '@' . $domain;
    my ( $found, $matchingkey, $result );
    for my $e (@$acl_ref) {
        $result      = 1;
        $matchingkey = $e;
        my ($key) = $e;
        if ( $key =~ /^(!+)(.*)\z/s ) {    # starts with an exclamation mark(s)
            $key = $2;
            $result = 1 - $result if ( length($1) & 1 );    # negate if odd
        }
        if ( $key =~ /^(.*?)\@(.*)\z/s ) {    # contains '@', check full address
            $found++
              if $localpart eq lc($1)
              && ( length( lc($2) ) == 0 || $domain eq lc($2) );
        }
        elsif ( $key =~ /^\.(.*)\z/s ) {      # leading dot: domain or subdomain
            my ($key_t) = lc($1);
            $found++ if $domain eq $key_t || $domain =~ /\Q$key_t\E\z/s;
        }
        else {    # match domain (but not its subdomains)
            $found++ if $domain eq lc($key);
        }
        last if $found;
    }
    $matchingkey = $result = undef if !$found;
    if ( !defined( $checked{"$addr acl"} ) ) {
        do_log(
            ( $found ? 3 : 6 ),
            "Whitelist check: $addr"
              . (
                !$found
                ? "doesn't match"
                : " matches entry \"$matchingkey\""
              )
        );
        $checked{"$addr acl"}++;
    }
    !wantarray ? $result : ( $result, $matchingkey );
}

#
#   This code is Copyright (C) 2001 Morgan Stanley Dean Witter, and
#   is distributed according to the terms of the GNU Public License
#   as found at <URL:http://www.fsf.org/copyleft/gpl.html>.
#
#
#   This program is distributed in the hope that it will be useful,
#   but WITHOUT ANY WARRANTY; without even the implied warranty of
#   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#   GNU General Public License for more details.
#
# Written by Bennett Todd <bet@rahul.net>

my $syntax =
    "syntax: $0 [--children=16] [--minperchild=100] "
  . "[--maxperchild=200] [--debugtrace=undef] "
  . "listen.addr:port talk.addr:port\n";

my $children    = 3;
my $minperchild = 100;
my $maxperchild = 200;
my $debugtrace  = undef;
GetOptions(
    "children=n"    => \$children,
    "minperchild=n" => \$minperchild,
    "maxperchild=n" => \$maxperchild,
    "debugtrace=s"  => \$debugtrace
  )
  or die $syntax;

die $syntax unless @ARGV == 2;
my ( $srcaddr, $srcport ) = split /:/, $ARGV[0];
my ( $dstaddr, $dstport ) = split /:/, $ARGV[1];
die $syntax unless defined($srcport) and defined($dstport);

# This should allow a kill on the parent to also blow away the
# children, I hope
my %children;
use vars qw($please_die);
$please_die = 0;
$SIG{TERM} = sub { $please_die = 1; };
$server = MSDW::SMTP::Server->new( interface => $srcaddr, port => $srcport );

if ( $daemonize != 0 ) {
    daemonize( $user, $group, $pidfile )
      or argh("Error: could not detach: $!");
}
else {
    print "Suriproxy starting. Staying in the foreground (see \$daemonize).\n";
}

do_log( 1, "Suriproxy v$version starting." );

# This block is the parent daemon, never does an accept, just herds
# a pool of children who accept and service connections, and
# occasionally kill themselves off

PARENT: while (1) {
    while ( scalar( keys %children ) >= $children ) {
        my $child = wait;
        delete $children{$child} if exists $children{$child};
        if ($please_die) { kill 15, keys %children; exit 0; }
    }
    my $pid = fork;
    argh("$0: fork failed: $!\n") unless defined $pid;
    last PARENT if $pid == 0;
    $children{$pid} = 1;
    select( undef, undef, undef, 0.1 );
    if ($please_die) { kill 15, keys %children; exit 0; }
}

# This block is a child service daemon. It inherited the bound
# socket created by SMTP::Server->new, it will service a random
# number of connection requests in [minperchild..maxperchild] then
# exit

my $lives = $minperchild + ( rand( $maxperchild - $minperchild ) );
my %opts;

#suri settings

$res->udp_timeout(5);

if ( defined $debugtrace ) {
    $opts{debug} = IO::File->new(">$debugtrace");
    $opts{debug}->autoflush(1);
}

while (1) {
    $server->accept(%opts);

    local $SIG{ALRM} = sub { die "Child server process timed out!\n" };

    alarm($child_timeout);

    my $client =
      MSDW::SMTP::Client->new( interface => $dstaddr, port => $dstport );
    my $banner = $client->hear
      or argh("FATAL ERROR: 1202 $!");

    #    $banner = "220 $debugtrace" if defined $debugtrace;
    $server->ok($banner)
      or argh("FATAL ERROR: 1222 $!");

    while ( my $what = $server->chat ) {

        if ( $what eq '.' ) {
            my $check = &suri( $server->{data} );

            $server->{data}->seek( 0, 0 )
              or argh("FATAL ERROR: 1142 $!");

            do_log( 5, "Check result: $check" );
            if ( $check =~ /^DENY/ ) {
                if ( $mode eq 'transparent' ) {
                    $server->ok("$deny_code $deny_msg $refer_msg.")
                      or argh("FATAL ERROR: 1132 $!");

                    last;

                    #next; #todo: continue the dialog
                }
                else {
                    $server->ok("250 OK - Discarded: $check.")
                      or argh("FATAL ERROR: 1102 $!");

                    #        last;
                    next;
                }
            }
            else {
                $client->yammer( $server->{data} )
                  or argh("FATAL ERROR: 1103 $!");
            }

        }
        else {
            $client->say($what)
              or argh("FATAL ERROR: 1104 $!");

        }

        #from spampd
        my $destresp = $client->hear
          or argh("FATAL ERROR: 1122 $!");
        $server->ok($destresp)
          or argh("Error in server->ok(client->hear): $!");

        if ( $server->{state} =~ /^data/i and $destresp =~ /^[45]\d{2}/ ) {
            $server->{state} = "err_after_data";
        }
        alarm($child_timeout);
    }
    $client = undef;
    delete $server->{"s"};
    exit 0 if $lives-- <= 0;
}

