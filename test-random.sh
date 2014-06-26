#!/bin/bash

. testlib.sh

n=${1:-5}
shift
args=$@

echo -n Generating tests...

rm -f random_tests/*
for ((i=0; i<$n; i++)); do
    f=random_tests/test_$i.c
    ./rndgen.py $f 0 3 6
done

echo

run_all_tests_in random_tests --assume-deterministic $args
report_test_results
