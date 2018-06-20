#!/usr/bin/perl

#
# Copyright (C) 2018 Joelle Maslak
# All Rights Reserved - See License
#

use strict;
use warnings;

use Test2::V0 0.000111;
use Net::Netmask;

my (@tests) = (
    {
        input  => [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
        output => '::',
    },
    {
        input  => [ 0, 1, 0, 2, 0, 3, 0, 4, 0, 5, 0, 6, 0, 7, 0, 8 ],
        output => '1:2:3:4:5:6:7:8',
    },
    {
        input  => [ 0, 1, 0, 2, 0, 3, 0, 0, 0, 0, 0, 6, 0, 7, 0, 8 ],
        output => '1:2:3::6:7:8',
    },
    {
        input  => [ 0, 0, 0, 0, 0, 3, 0, 4, 0, 5, 0, 6, 0, 7, 0, 8 ],
        output => '::3:4:5:6:7:8',
    },
    {
        input  => [ 0, 1, 0, 2, 0, 3, 0, 4, 0, 5, 0, 6, 0, 0, 0, 0 ],
        output => '1:2:3:4:5:6::',
    },
    {
        input  => [ 0, 0, 0, 0, 0, 3, 0, 4, 0, 5, 0, 6, 0, 0, 0, 0 ],
        output => '::3:4:5:6:0:0',
    },
    {
        input  => [ 0, 0, 0, 0, 0, 3, 0, 4, 0, 5, 0, 0, 0, 0, 0, 0 ],
        output => '0:0:3:4:5::',
    },
    {
        input  => [ 0, 1, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0 ],
        output => '1::5:0:0:0',
    },
    {
        input  => [ 0, 1, 0, 0, 0, 0, 0, 0, 0, 95, 0, 0, 0, 0, 0, 0 ],
        output => '1::5f:0:0:0',
    },
);

foreach my $test (@tests) {
    my $raw = join '', map { chr($_) } @{ $test->{input} };
    my $got = Net::Netmask::raw2ascii($raw, 'IPv6');

    is($got, $test->{output}, $test->{output});

    my $reverse = Net::Netmask::ascii2raw($test->{output}, 'IPv6');
    is($reverse, $raw, 'ascii2raw for ' . $test->{output});
}

done_testing;

1;


