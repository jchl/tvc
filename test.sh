#!/bin/bash

. testlib.sh

args=$@

echo -n Generating tests...

rm -f generated_tests/*
./mktests.py

echo

run_all_tests_in basic_tests $args
run_all_tests_in generated_tests $args
report_test_results
