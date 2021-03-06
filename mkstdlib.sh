#!/bin/sh

set -e # fail on error

TVCDIR=${TVCDIR:-.} # default to current directory

. $TVCDIR/vars.sh

outfile=$1
shift
args=$@

# It is necessary to use version 3.0 of clang, as the version of libllvm used by llvm2coqtext
# doesn't understand the LLVM bitcode format generated by more recent versions of clang.
$TVCDIR/main.d.byte none $CSEMDIR/corelib/std.core $CSEMDIR/corelib/impls/$IMPL.impl dummy.core $outfile --dump-stdlib-and-impl $args
