#!/bin/sh

set -e # fail on error

TVCDIR=${TVCDIR:-.} # default to current directory

. $TVCDIR/vars.sh

f=$1

CSMITHARGS="--no-arrays --no-pointers --no-structs --no-unions \
  --no-volatiles --no-consts \
  --no-compound-assignment --no-pre-incr-operator --no-pre-decr-operator --no-post-incr-operator --no-post-decr-operator \
  --concise --nomain --no-safe-math \
  --max-funcs 4"

rm -f $f
until [ -f $f ] && ! grep -q g_ $f; do
    $CSMITHDIR/src/csmith $CSMITHARGS -o $f
done

sed -i '' -e 's/#include "csmith.h"//' $f

sed -i '' -e 's/uint8_t/unsigned char/g' $f
sed -i '' -e 's/int8_t/signed char/g' $f
sed -i '' -e 's/uint16_t/unsigned short/g' $f
sed -i '' -e 's/int16_t/signed short/g' $f
sed -i '' -e 's/uint32_t/unsigned int/g' $f
sed -i '' -e 's/int32_t/signed int/g' $f
sed -i '' -e 's/uint64_t/unsigned long/g' $f
sed -i '' -e 's/int64_t/signed long/g' $f

sed -i '' -e 's/-= 1/--/g' $f
sed -i '' -e 's/\+= 1/\+\+/g' $f

cat >>$f <<EOF

int main() {
    return func_1();
}
EOF

# XXX An alternative to the above which works even if there are global variables.
#sed -i -e 's/^.*func_1(void)/int main(void)/g' $f
