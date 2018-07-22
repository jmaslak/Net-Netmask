#!/usr/bin/perl -w

use strict;

use Test2::V0;

use Net::Netmask qw(
  cidrs2cidrs
  cidrs2contiglists
  cidrs2inverse
  cmpblocks
  dumpNetworkTable
  findAllNetblock
  findNetblock
  findOuterNetblock
  range2cidrlist
  sameblock
  sort_by_ip_address
);
use Carp qw(verbose);

MAIN: {
    # Note that _ in the addr gets replaced with a '#'
    #  addr                       mask          base            newmask        bits mb proto todo
    my @rtests = qw(
      209.157.68.22:255.255.224.0 u             209.157.64.0    255.255.224.0    19 18 IPv4     0
      209.157.68.22               255.255.224.0 209.157.64.0    255.255.224.0    19 18 IPv4     0
      209.157.70.33               0xffffe000    209.157.64.0    255.255.224.0    19 18 IPv4     0
      209.157.70.33/19            u             209.157.64.0    255.255.224.0    19 18 IPv4     0
      209.157.70.33               u             209.157.70.33   255.255.255.255  32 32 IPv4     0
      140.174.82                  u             140.174.82.0    255.255.255.0    24 23 IPv4     0
      140.174                     u             140.174.0.0     255.255.0.0      16 15 IPv4     0
      10                          u             10.0.0.0        255.0.0.0        8  7  IPv4     0
      10/8                        u             10.0.0.0        255.0.0.0        8  7  IPv4     0
      209.157.64/19               u             209.157.64.0    255.255.224.0    19 18 IPv4     0
      209.157.64.0-209.157.95.255 u             209.157.64.0    255.255.224.0    19 18 IPv4     0
      216.140.48.16/32            u             216.140.48.16   255.255.255.255  32 28 IPv4     0
      209.157/17                  u             209.157.0.0     255.255.128.0    17 16 IPv4     0
      default                     u             0.0.0.0         0.0.0.0          0  0  IPv4     0
      209.157.68.22_0.0.31.255    u             209.157.64.0    255.255.224.0    19 18 IPv4     0
      2001:db8::/32               u             2001:db8::      ffff:ffff::      32 29 IPv6     0
      2001:db8:100::/48           u             2001:db8:100::  ffff:ffff:ffff:: 48 40 IPv6     0
      2001:db8:100::              u             2001:db8:100::  ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff 128  40 IPv6  0
      2001:db8:100::1             u             2001:db8:100::1 ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff 128 128 IPv6  0
      default6                    u             ::              ::               0  0  IPv6  0
    );

    my @store = qw(
      209.157.64.0/19
      default
      default6
      209.157.81.16/28
      209.157.80.0/20
      2001:db8:100::/48
    );

    my @lookup = qw(
      209.157.75.75     209.157.64.0/19
      209.157.32.10     0.0.0.0/0
      209.157.81.18     209.157.81.16/28
      209.157.81.14     209.157.80.0/20
      2001:db8:100::3   2001:db8:100::/48
      2001:db8:200::3   ::/0
    );

    my @store2 = qw(
      209.157.64.0/19
      default
      default6
      209.157.81.16/28
      209.157.80.0/24
      2001:db8:100::/48
    );

    my @lookup2 = qw(
      209.157.75.75     209.157.64.0/19
      209.157.32.10     0.0.0.0/0
      209.157.81.18     209.157.81.16/28
      209.157.81.14     209.157.64.0/19
      2001:db8:100::3   2001:db8:100::/48
      2001:db8:200::3   ::/0
    );

    my $debug = 0;
    my $x;

    my ( $addr, $mask, $base, $newmask, $bits, $max, $proto, $todo );
    while ( ( $addr, $mask, $base, $newmask, $bits, $max, $proto, $todo ) =
        splice( @rtests, 0, 8 ) )
    {

        $addr =~ s/_/#/g;

        diag "$addr $mask $base $newmask $bits $max $proto $todo";

        $mask    = undef if $mask eq 'u';
        $newmask = undef if $newmask eq 'u';

        my $test = sub {
            $x = Net::Netmask->new( $addr, $mask );
            ok( $x, "parsed $addr " );

            if ( defined($x) ) {
                is( $x->base(),     $base,    "base of $addr" );
                is( $x->mask(),     $newmask, "mask of $addr" );
                is( $x->maxblock(), $max,     "maxblock of $addr" );
                is( $x->bits(),     $bits,    "bits of $addr" );
                is( $x->protocol(), $proto,   "protocol of $addr" );
            }
        };

        if ($todo) {
            todo 'marked as todo' => $test;
        } else {
            $test->();
        }
    }

    my @y;

    $x = Net::Netmask->new('209.157.64.0/19');
    is( $x->size(),     8192,         "size of 209.157.64.0/19" );
    is( $x->hostmask(), '0.0.31.255', "hostmask of 209.157.64.0/19" );

    @y = $x->inaddr();
    print "# REVERSE: @y\n";
    is( $y[0],        '64.157.209.in-addr.arpa' );
    is( $y[ 31 * 3 ], '95.157.209.in-addr.arpa' );
    ok( !defined( $y[ 32 * 3 ] ), '!defined $y[32*3]' );

    $x = Net::Netmask->new('140.174.82.4/32');
    is( $x->size(), 1, "size of 140.174.82.4/32" );

    is( ( $x->inaddr() )[0], '82.174.140.in-addr.arpa' );

    $x = Net::Netmask->new('140.174.82.64/27');
    is( ( $x->inaddr() )[1], 64 );
    is( ( $x->inaddr() )[2], 95 );

    $x = Net::Netmask->new('any');
    ok( $x->size() == 4294967296, 'size of any netblock' );
    
    $x = Net::Netmask->new('::/0');
    is( $x->size(), '340282366920938463463374607431768211456', "size of ::/0");
    @y = $x->inaddr();
    print "# REVERSE: @y\n";
    is( $y[0], 'ip6.arpa' );

    $x = Net::Netmask->new('2001:db8:100::3');
    is( $x->size(), '1', "size of 2001:db8:100::3");
    @y = $x->inaddr();
    print "# REVERSE: @y\n";
    is( $y[0], '3.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.1.0.8.b.d.0.1.0.0.2.ip6.arpa');

    $x = Net::Netmask->new('2001:db8:100::/48');
    is( $x->size(), '1208925819614629174706176', "size of 2001:db8:100::/48");
    @y = $x->inaddr();
    print "# REVERSE: @y\n";
    is( $y[0], '0.0.1.0.8.b.d.0.1.0.0.2.ip6.arpa');

    $x = Net::Netmask->new('2001:db8:100::/49');
    is( $x->size(), '604462909807314587353088', "size of 2001:db8:100::/48");
    @y = $x->inaddr();
    print "# REVERSE: @y\n";
    is( $y[0], '0.0.0.1.0.8.b.d.0.1.0.0.2.ip6.arpa');
    is( $y[1], '1.0.0.1.0.8.b.d.0.1.0.0.2.ip6.arpa');
    is( $y[7], '7.0.0.1.0.8.b.d.0.1.0.0.2.ip6.arpa');
    ok( !defined( $y[8] ), '!defined $y[8]');


    $x = Net::Netmask->new('209.157.64.0/27');
    @y = $x->enumerate();
    is( $y[0],  '209.157.64.0' );
    is( $y[31], '209.157.64.31' );
    ok( !defined( $y[32] ), '!defiend($y[32])' );
    @y = $x->enumerate(31);
    is( $y[0],  '209.157.64.0' );
    is( $y[15], '209.157.64.30' );
    ok( !defined( $y[16] ), '!defined($y[16]' );

    $x = Net::Netmask->new('10.2.0.16/19');
    @y = $x->enumerate();
    is( $y[0],    '10.2.0.0' );
    is( $y[8191], '10.2.31.255' );
    ok( !defined( $y[8192] ), '!defined($y[8192])' );

    my $table  = {};
    my $table9 = {};

    {
        for my $b (@store) {
            $x = Net::Netmask->new($b);
            $x->storeNetblock();
        }
    }

    {
        for my $b (@store2) {
            $x = Net::Netmask->new($b);
            $x->storeNetblock($table);
            $x->storeNetblock($table9);
        }
    }

    my $result;
    while ( ( $addr, $result ) = splice( @lookup, 0, 2 ) ) {
        my $nb = findNetblock($addr);
        printf "# lookup(%s): %s, wanting %s.\n", $addr, $nb->desc(), $result;
        is( $nb->desc(), $result, "$addr / $result" );
    }

    while ( ( $addr, $result ) = splice( @lookup2, 0, 2 ) ) {
        my $nb = findNetblock( $addr, $table );
        printf "# lookup(%s): %s, wanting %s.\n", $addr, $nb->desc(), $result;
        is( $nb->desc(), $result, "$addr / $result" );
    }

    $newmask = Net::Netmask->new("192.168.1.0/24");
    is( $newmask->broadcast(), "192.168.1.255" );
    is( $newmask->next(),      "192.168.2.0" );
    ok( $newmask->match("192.168.1.0"),   'match 192.168.1.0' );
    ok( $newmask->match("192.168.1.255"), 'match 192.168.1.255' );
    ok( $newmask->match("192.168.1.63"),  'match 192.168.1.63' );

    ok( !$newmask->match("192.168.0.255"), 'match 192.168.0.255' );
    ok( !$newmask->match("192.168.2.0"),   'match 192.168.2.0' );
    ok( !$newmask->match("10.168.2.0"),    'match 10.168.2.0' );
    ok( !$newmask->match("209.168.2.0"),   'match 209.168.2.0' );

    is( $newmask->nth(1),  '192.168.1.1' );
    is( $newmask->nth(-1), '192.168.1.255' );
    is( $newmask->nth(-2), '192.168.1.254' );
    is( $newmask->nth(0),  '192.168.1.0' );
    is( $newmask->nth( 1, 31 ), '192.168.1.2' );
    is( $newmask->nth(256),  undef );
    is( $newmask->nth(-257), undef );

    ok( $newmask->match('192.168.1.1') == 1,     'match 192.168.1.1' );
    ok( $newmask->match('192.168.1.100') == 100, 'match 192.168.1.100' );
    ok( $newmask->match('192.168.1.255') == 255, 'match 192.168.1.255' );

    ok( ( $newmask->match('192.168.2.1') == 0 ), 'match 192.168.2.1' );
    ok( !( $newmask->match('192.168.2.1') ), 'match 192.168.2.1' );
    ok( ( ( 0 + $newmask->match('192.168.1.0') ) == 0 ), '0 + match 192.168.1.0' );
    ok( ( $newmask->match('192.168.1.0') ), 'match 192.168.1.0' );

    my $bks;
    my $block = Net::Netmask->new('209.157.64.1/32');
    $block->storeNetblock($bks);
    ok( findNetblock( '209.157.64.1', $bks ), 'findNetBlock 209.157.64.1 / 209.157.64.1/32' );

    my @store3 = qw(
      216.240.32.0/19
      216.240.40.0/24
      216.240.40.0/27
      216.240.40.4/30
    );
    my $table3 = {};
    my $table8 = {};
    my $table7 = {};
    my $table6 = {};
    for my $b (@store3) {
        $x = Net::Netmask->new($b);
        $x->storeNetblock($table3);
        $x->storeNetblock($table8);
        $x->storeNetblock($table7);
        $x->storeNetblock($table6);
    }
    lookeq( $table3, "216.240.40.5",   "216.240.40.4/30" );
    lookeq( $table3, "216.240.40.1",   "216.240.40.0/27" );
    lookeq( $table3, "216.240.40.50",  "216.240.40.0/24" );
    lookeq( $table3, "216.240.50.150", "216.240.32.0/19" );
    lookeq( $table3, "209.157.32.32",  undef );
    fdel( "216.240.40.1", "216.240.40.0/27", $table3 );
    lookeq( $table3, "216.240.40.5",   "216.240.40.4/30" );
    lookeq( $table3, "216.240.40.1",   "216.240.40.0/24" );
    lookeq( $table3, "216.240.40.50",  "216.240.40.0/24" );
    lookeq( $table3, "216.240.50.150", "216.240.32.0/19" );
    lookeq( $table3, "209.157.32.32",  undef );
    fdel( "216.240.50.150", "216.240.32.0/19", $table3 );
    lookeq( $table3, "216.240.40.5",   "216.240.40.4/30" );
    lookeq( $table3, "216.240.40.1",   "216.240.40.0/24" );
    lookeq( $table3, "216.240.40.50",  "216.240.40.0/24" );
    lookeq( $table3, "216.240.50.150", undef );
    lookeq( $table3, "209.157.32.32",  undef );
    fdel( "216.240.40.4", "216.240.40.4/30", $table3 );
    lookeq( $table3, "216.240.40.5",   "216.240.40.0/24" );
    lookeq( $table3, "216.240.40.1",   "216.240.40.0/24" );
    lookeq( $table3, "216.240.40.50",  "216.240.40.0/24" );
    lookeq( $table3, "216.240.50.150", undef );
    lookeq( $table3, "209.157.32.32",  undef );
    fdel( "216.240.40.4", "216.240.40.0/24", $table3 );
    lookeq( $table3, "216.240.40.5",   undef );
    lookeq( $table3, "216.240.40.1",   undef );
    lookeq( $table3, "216.240.40.50",  undef );
    lookeq( $table3, "216.240.50.150", undef );
    lookeq( $table3, "209.157.32.32",  undef );

    my (@c) = range2cidrlist( "66.33.85.239", "66.33.85.240" );
    my $dl = dlist(@c);
    is( $dl, '66.33.85.239/32 66.33.85.240/32', 'match cidrlist 1' );

    (@c) = range2cidrlist( "66.33.85.240", "66.33.85.239" );
    $dl = dlist(@c);
    is( $dl, '66.33.85.239/32 66.33.85.240/32', 'match cidrlist 2' );

    (@c) = range2cidrlist( '216.240.32.128', '216.240.36.127' );
    $dl = dlist(@c);
    is(
        $dl,
        '216.240.32.128/25 216.240.33.0/24 216.240.34.0/23 216.240.36.0/25',
        'match cidrlist 3'
    );

    my @d;
    @d = ( @c[ 0, 1, 3 ] );

    my (@e) = cidrs2contiglists(@d);

    is( @e, 2 );

    is( dlist( @{ $e[0] } ), '216.240.32.128/25 216.240.33.0/24' );
    is( dlist( @{ $e[1] } ), '216.240.36.0/25' );

    my (@iplist) = generate(500);

    my (@sorted1) = sort_by_ip_address(@iplist);

    my (@blist)   = map { Net::Netmask->new($_) } @iplist;
    my (@clist)   = sort @blist;
    my (@sorted2) = map { $_->base() } @clist;
    my (@dlist)   = sort @blist;
    my (@sorted3) = map { $_->base() } @dlist;

  SKIP: {
        skip 2 if $] < 5.006_001;
        is( "@sorted1", "@sorted2" );
        is( "@sorted1", "@sorted3" );
    }

    my $q144 = Net::Netmask->new('216.240.32.0/25');

    for my $i (qw(216.240.32.0/24 216.240.32.0/26 216.240.33.0/25)) {
        my $q144p = Net::Netmask->new($i);

        print "# working on $i\n";
        ok( !( $q144 eq $q144p ) );
        ok( !( $q144 == $q144p ) );
        ok( !( sameblock( $q144, $i ) ) );
        ok( !( $q144->sameblock($i) ) );
        ok( cmpblocks( $q144, $i ) );
        ok( $q144->cmpblocks($i) );
    }

    my $q144pp = Net::Netmask->new('216.240.32.0/25');
    ok( ( $q144 == $q144pp ) );
    ok( ( $q144 eq $q144pp ) );
    ok( ( $q144->desc eq "$q144" ) );
    ok( $q144->sameblock('216.240.32.0/25') );
    ok( sameblock( $q144, '216.240.32.0/25' ) );

    ok( !( cmpblocks( $q144, '216.240.32.0/25' ) ) );
    ok( !( $q144->cmpblocks('216.240.32.0/25') ) );

    my $dnts = join( ' ', dumpNetworkTable($table9) );
    is( $dnts,
        '0.0.0.0/0 209.157.64.0/19 209.157.80.0/24 209.157.81.16/28 ::/0 2001:db8:100::/48' );

    # 216.240.32.0/19
    # 216.240.40.0/24
    # 216.240.40.0/27
    # 216.240.40.4/30

    lookouter( $table8, "216.240.40.5",   "216.240.32.0/19" );
    lookouter( $table8, "216.240.40.1",   "216.240.32.0/19" );
    lookouter( $table8, "216.240.40.50",  "216.240.32.0/19" );
    lookouter( $table8, "216.240.50.150", "216.240.32.0/19" );
    lookouter( $table8, "209.157.32.32",  undef );
    fdel( "216.240.32.10", "216.240.32.0/19", $table8 );
    lookouter( $table8, "216.240.40.5",   "216.240.40.0/24" );
    lookouter( $table8, "216.240.40.1",   "216.240.40.0/24" );
    lookouter( $table8, "216.240.40.50",  "216.240.40.0/24" );
    lookouter( $table8, "216.240.50.150", undef );
    lookouter( $table8, "209.157.32.32",  undef );
    fdel( "216.240.40.150", "216.240.40.0/24", $table8 );
    lookouter( $table8, "216.240.40.5",   "216.240.40.0/27" );
    lookouter( $table8, "216.240.40.1",   "216.240.40.0/27" );
    lookouter( $table8, "216.240.40.50",  undef );
    lookouter( $table8, "216.240.50.150", undef );
    lookouter( $table8, "209.157.32.32",  undef );
    fdel( "216.240.40.3", "216.240.40.0/27", $table8 );
    lookouter( $table8, "216.240.40.5",   "216.240.40.4/30" );
    lookouter( $table8, "216.240.40.1",   undef );
    lookouter( $table8, "216.240.40.50",  undef );
    lookouter( $table8, "216.240.50.150", undef );
    lookouter( $table8, "209.157.32.32",  undef );
    fdel( "216.240.40.4", "216.240.40.4/30", $table8 );
    lookouter( $table8, "216.240.40.5",   undef );
    lookouter( $table8, "216.240.40.1",   undef );
    lookouter( $table8, "216.240.40.50",  undef );
    lookouter( $table8, "216.240.50.150", undef );
    lookouter( $table8, "209.157.32.32",  undef );

    lookouterO( $table7, "216.240.40.5/30",   "216.240.32.0/19" );
    lookouterO( $table7, "216.240.40.5/29",   "216.240.32.0/19" );
    lookouterO( $table7, "216.240.40.50/24",  "216.240.32.0/19" );
    lookouterO( $table7, "216.240.50.150/23", "216.240.32.0/19" );
    lookouterO( $table7, "209.157.32.32",     undef );
    fdel( "216.240.32.10", "216.240.32.0/19", $table7 );
    lookouterO( $table7, "216.240.40.5/30",   "216.240.40.0/24" );
    lookouterO( $table7, "216.240.40.5/29",   "216.240.40.0/24" );
    lookouterO( $table7, "216.240.40.50/24",  "216.240.40.0/24" );
    lookouterO( $table7, "216.240.50.150/23", undef );
    lookouterO( $table7, "209.157.32.32",     undef );
    fdel( "216.240.40.150", "216.240.40.0/24", $table7 );
    lookouterO( $table7, "216.240.40.5/30",   "216.240.40.0/27" );
    lookouterO( $table7, "216.240.40.5/29",   "216.240.40.0/27" );
    lookouterO( $table7, "216.240.40.50/24",  undef );
    lookouterO( $table7, "216.240.50.150/23", undef );
    lookouterO( $table7, "209.157.32.32",     undef );
    fdel( "216.240.40.3", "216.240.40.0/27", $table7 );
    lookouterO( $table7, "216.240.40.5/30",   "216.240.40.4/30" );
    lookouterO( $table7, "216.240.40.5/29",   undef );
    lookouterO( $table7, "216.240.40.50/24",  undef );
    lookouterO( $table7, "216.240.50.150/23", undef );
    lookouterO( $table7, "209.157.32.32",     undef );
    fdel( "216.240.40.4", "216.240.40.4/30", $table7 );
    lookouterO( $table7, "216.240.40.5/30",   undef );
    lookouterO( $table7, "216.240.40.1/29",   undef );
    lookouterO( $table7, "216.240.40.50/24",  undef );
    lookouterO( $table7, "216.240.50.150/23", undef );
    lookouterO( $table7, "209.157.32.32/8",   undef );

    ctest( "10.20.30.0/24",      "10.20.30.0/25" );
    ctest( "10.20.30.0/23",      "10.20.30.0/24" );
    ctest( "10.20.30.0/24",      "10.20.30.128/25" );
    ctest( "0.0.0.0/8",          "0.255.255.255/32" );
    ctest( "255.255.255.255/32", "255.255.255.255/32" );
    ctest( "255.255.255.0/24",   "255.255.255.255/32" );

    ctest( "66.106.19.144/28", "66.106.19.152/29" );
    ctest( "66.106.19.144/28", "66.106.19.144/29" );

    ctestno( "66.106.19.144/28", "66.106.19.168/29" );
    ctestno( "66.106.19.144/28", "198.175.15.10/29" );
    ctestno( "66.106.19.144/28", "66.106.19.160/29" );

    (@c) =
      cidrs2cidrs(
        multinew(qw(216.240.32.0/25 216.240.32.128/25 216.240.33.0/25 216.240.34.0/24)) );
    $dl = dlist(@c);
    is( $dl, '216.240.32.0/24 216.240.33.0/25 216.240.34.0/24' );

    (@c) = cidrs2cidrs(
        multinew(
            qw(216.240.32.0/32 216.240.32.1/32 216.240.32.2/32 216.240.32.3/32 216.240.32.4/32))
    );
    $dl = dlist(@c);
    is( $dl, '216.240.32.0/30 216.240.32.4/32' );

    (@c) = cidrs2cidrs(
        multinew(
            qw(216.240.32.64/28 216.240.32.0/25 216.240.32.128/25 216.240.33.0/25 216.240.34.0/24))
    );
    $dl = dlist(@c);
    is( $dl, '216.240.32.0/24 216.240.33.0/25 216.240.34.0/24' );

    $block = Net::Netmask->new( '172.2.4.0', '255.255.255.0' );
    $table = {};
    $block->storeNetblock($table);
    my @bl = findAllNetblock( '172.2.4.1', $table );
    is( $#bl, 0 );

    $block->tag( 'a', 'b' );
    $block->tag( 'b', 'c' );
    $block->tag( 'c', 'x' );
    $block->tag( 'c', undef );
    $block->tag( 'd', 'x' );
    $block->tag('d');

    is( $block->tag('a'), 'b' );
    is( $block->tag('b'), 'c' );
    is( $block->tag('c'), undef );
    is( $block->tag('d'), 'x' );
    is( $block->tag('a'), 'b' );

    (@c) = cidrs2inverse(
        '216.240.32.0/22',
        (
            multinew(
                qw(216.240.32.64/28 216.240.32.0/25 216.240.32.128/25 216.240.33.0/25 216.240.34.0/24)
            )
        )
    );
    $dl = dlist(@c);
    is( $dl, '216.240.33.128/25 216.240.35.0/24' );

    (@c) = cidrs2inverse(
        '216.240.32.0/22',
        (
            multinew(
                qw(215.0.0.0/16 216.240.32.64/28 216.240.32.0/25 216.240.32.128/25 216.240.33.0/25 216.240.34.0/24 216.240.45.0/24)
            )
        )
    );
    $dl = dlist(@c);
    is( $dl, '216.240.33.128/25 216.240.35.0/24' );

    (@c) = cidrs2inverse(
        '216.240.32.0/22',
        (
            multinew(
                qw(216.240.0.0/16 215.0.0.0/16 216.240.32.64/28 216.240.32.0/25 216.240.32.128/25 216.240.33.0/25 216.240.34.0/24 216.240.45.0/24)
            )
        )
    );
    $dl = dlist(@c);
    is( $dl, '' );

    my $table77 = {};
    my $block77 = new2 Net::Netmask( "10.1.2.0/24", $table77 );
    $block77->storeNetblock();
    is( findNetblock( "10.2.1.0", $table77 ), undef );

    {
        my $bl = Net::Netmask->new("192.168.0.0/23");
        my @t  = (
            undef, '192.168.2.0/23',    # => would turn undef into "undef"
            10 => '192.168.20.0/23',
            7  => '192.168.14.0/23',
            -1 => '192.167.254.0/23',
        );
        while (@t) {
            my $arg = shift(@t);
            $result = shift(@t);
            is( $bl->nextblock($arg) . "", $result, "$result" );
        }
    }

    {
        my $obj1     = new2 Net::Netmask('1.0.0.4/31');
        my $obj2     = new2 Net::Netmask('1.0.0.4/32');
        my @leftover = cidrs2inverse( $obj1, $obj2 );
        # print "leftover = @leftover\n";
        is( @leftover,      1 );
        is( "$leftover[0]", "1.0.0.5/32" );
    }

    {
        my $obj1     = new2 Net::Netmask('1.0.0.4/32');
        my $obj2     = new2 Net::Netmask('1.0.0.0/8');
        my @leftover = cidrs2inverse( $obj1, $obj2 );
        is( @leftover, 0, "@leftover" );
    }

    {
        my $obj1     = new2 Net::Netmask('1.0.0.4/32');
        my $obj2     = new2 Net::Netmask('1.0.0.4/32');
        my @leftover = cidrs2inverse( $obj1, $obj2 );
        is( @leftover, 0, "@leftover" );
    }

    {
        my $obj1     = new2 Net::Netmask('1.0.0.4/32');
        my $obj2     = new2 Net::Netmask('1.0.0.6/32');
        my @leftover = cidrs2inverse( $obj1, $obj2 );
        is( @leftover,      1 );
        is( "$leftover[0]", '1.0.0.4/32' );
    }

    {
        my $obj1     = new2 Net::Netmask('1.0.0.4/31');
        my $obj2     = new2 Net::Netmask('1.0.0.5/32');
        my @leftover = cidrs2inverse( $obj1, $obj2 );
        is( @leftover,      1 );
        is( "$leftover[0]", '1.0.0.4/32' );
    }

    {
        my $obj1     = new2 Net::Netmask('1.0.0.4/31');
        my $obj2     = new2 Net::Netmask('1.0.0.4/32');
        my @leftover = cidrs2inverse( $obj1, $obj2 );
        is( @leftover,      1 );
        is( "$leftover[0]", '1.0.0.5/32' );
    }

    {
        my $obj1 = new2 Net::Netmask('217.173.192.0/21');
        my $obj2 = new2 Net::Netmask('217.173.200.0/21');
        is( "$obj1",                '217.173.192.0/21' );
        is( "$obj2",                '217.173.200.0/21' );
        is( $obj1->contains($obj2), 0 );
        is( $obj2->contains($obj1), 0 );
    }

    {
        my $obj1 = new2 Net::Netmask('217.173.192.0/21');
        ok( $obj1->contains("217.173.192.0/24") );
        ok( !$obj1->contains("217.173.200.0/21") );
    }

    {
        my $warnings = '';
        local ( $SIG{__WARN__} ) = sub { $warnings = $_[0] };
        my $blk = findNetblock( "127.0.0.", { 1 => [] } );
        is( $warnings, '' );
    }

    done_testing();
}

sub lookeq {
    my ( $table, $value, $result ) = @_;
    my $found = findNetblock( $value, $table );
    if ($result) {
        is( $found->desc, $result, "value='$value' found=@{[$found->desc]}" );
    } else {
        ok( !$found, $value );
    }
    return;
}

sub fdel {
    my ( $value, $result, $table ) = @_;
    my $found = findNetblock( $value, $table );
    #print "search for $value, found and deleting @{[ $found->desc ]} eq $result\n";
    is( $found->desc, $result, "$value / $result" );
    $found->deleteNetblock($table);
    return;
}

sub dlist {
    my (@bl) = @_;
    return join( ' ', map { $_->desc() } @bl );
}

sub generate {
    my $count = shift || 10000;
    my @list;
    $list[ $count - 1 ] = '';    ## preallocate
    for ( my $i = 0; $i < $count; $i++ ) {
        my $class = int( rand(3) );
        if ( $class == 0 ) {
            ## class A ( 1.0.0.0 - 126.255.255.255 )
            $list[$i] = int( rand(126) ) + 1;
        } elsif ( $class == 1 ) {
            ## class B ( 128.0.0.0 - 191.255.255.255 )
            $list[$i] = int( rand(64) ) + 128;
        } else {
            ## class C ( 192.0.0.0 - 223.255.255.255 )
            $list[$i] = int( rand(32) ) + 192;
        }
        $list[$i] .= '.' . int( rand(256) );
        $list[$i] .= '.' . int( rand(256) );
        $list[$i] .= '.' . int( rand(256) );
    }
    return @list;
}

sub by_net_netmask_block2 {
    return $a->{'IBASE'} <=> $b->{'IBASE'}
      || $a->{'BITS'} <=> $b->{'BITS'};
}

sub lookouter {
    my ( $table, $value, $result ) = @_;
    my $found = findOuterNetblock( $value, $table );
    if ($result) {
        is( $found->desc, $result, "value = $value, result = $result" );
    } else {
        ok( !$found, "value = $value" );
    }

    return;
}

sub lookouterO {
    my ( $table, $value, $result ) = @_;
    my $block = Net::Netmask->new2($value);
    my $found = findOuterNetblock( $block, $table );
    if ($result) {
        is( $found->desc, $result, "value = $value" );
    } else {
        ok( !$found );
    }
    return;
}

sub ctest {
    my $a = Net::Netmask->new(shift);
    my $b = Net::Netmask->new(shift);

    print "# ctest($a, $b)\n";
    ok( $a->contains($a) );
    ok( $b->contains($b) );
    ok( $a->contains($b) );
    ok( ( $a->sameblock($b) || !$b->contains($a) ) );
    return;
}

sub ctestno {
    my $a = Net::Netmask->new(shift);
    my $b = Net::Netmask->new(shift);

    print "# ctestno($a, $b)\n";
    ok( !$a->contains($b) );
    ok( !$b->contains($a) );
    return;
}

sub multinew {
    return map { Net::Netmask->new($_) } @_;
}

