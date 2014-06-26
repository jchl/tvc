run=0
passed=0
failed=0

function run_all_tests_in {
    d=$1
    shift
    args=$@
    for f in $d/*.c; do
        echo -n "Running $f..."
        base=${f%.c}
        ./runtvc -t $base $args > ${base}.out 2>&1
        if [ $? -eq 0 ]; then
            echo " PASSED"
            passed=$(($passed + 1))
        else
            echo " FAILED (see ${base}.out for details)"
            failed=$(($failed + 1))
        fi
        run=$(($run + 1))
    done
}

function report_test_results {
    echo
    if [ $failed -ne 0 ]; then
        echo "$failed of $run test(s) failed"
        exit 1
    else
        echo "All $run test(s) passed"
    fi
}
