BASEDIR=/Users/jchl/Dropbox/Work/Project

CSEMDIR=$BASEDIR/csem
CLANGDIR=/Users/jchl/Desktop/ExtraProjectStuff/clang+llvm-3.0-x86_64-apple-darwin11/bin
LLVMDIR=$BASEDIR/llvm-3.0.install
VELLVMDIR=$BASEDIR/vellvm-coq84pl2/release/vol/src
EXTRALIBSDIR=$BASEDIR/vellvm-coq84pl2/release/vol/extralibs
CSMITHDIR=$BASEDIR/csmith
LEMDIR=~/lem

IMPL=gcc_4.9.0_x86_64-apple-darwin10.8.0

COQINCLUDEOPTS="-R coq Tvc -R proofs Tvc -R $CSEMDIR/_coq Csem -I $LEMDIR/coq-lib -I $VELLVMDIR/Vellvm -I $VELLVMDIR/Vellvm/ott -I $VELLVMDIR/Vellvm/monads -I $VELLVMDIR/Vellvm/compcert -I $VELLVMDIR/Vellvm/GraphBasics -I $VELLVMDIR/Vellvm/Dominators -I $EXTRALIBSDIR/metatheory_8.4 -I $EXTRALIBSDIR/Coq-Equations/src -R $EXTRALIBSDIR/Coq-Equations/theories Equations"
