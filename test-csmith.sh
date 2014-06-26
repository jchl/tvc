#!/bin/bash

. testlib.sh

n=${1:-5}
shift
args=$@

echo -n Generating tests...

rm -f csmith_tests/*
for ((i=0; i<$n; i++)); do
    f=csmith_tests/test_$i.c
    ./csmith.sh $f
done

echo

run_all_tests_in csmith_tests --skeleton $args
report_test_results
