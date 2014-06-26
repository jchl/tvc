#!/usr/bin/env python

from csyntax import *

tvc_args = '// tvc-args: --main f'

####################################################################################################
# Test all (integer) return types with positive and negative values.
####################################################################################################
for t in types:
    for (s, v) in (('pos', 7), ('neg', -7)):
        with file('generated_tests/return_%s_%s.c' % (t.replace(' ', '_'), s), 'w') as f:
            print >>f, tvc_args + (' --ret-unsigned' if ('unsigned' in t) else '')
            print >>f, '%s f() {' % t
            print >>f, '  return %d;' % v
            print >>f, '}'
            print >>f, dummy_main_fn

####################################################################################################
# Test returning the minimum and maximum value of each (integer) type.
####################################################################################################
import limits

for t in types:
    (min_val, max_val) = limits.int_limits[t]
    for (s, v) in (('min', min_val), ('max', max_val)):
        with file('generated_tests/return_%s_%s.c' % (t.replace(' ', '_'), s), 'w') as f:
            print >>f, tvc_args + (' --ret-unsigned' if ('unsigned' in t) else '')
            print >>f, '%s f() {' % t
            print >>f, '  return %#x;' % v
            print >>f, '}'
            print >>f, dummy_main_fn

####################################################################################################
# Test all (integer) argument types.
####################################################################################################
for t in types:
    with file('generated_tests/arg_%s.c' % t.replace(' ', '_'), 'w') as f:
        print >>f, tvc_args + (' --arg-unsigned 0' if ('unsigned' in t) else '')
        print >>f, 'int f(%s x) {' % t
        print >>f, '  return 9;'
        print >>f, '}'
        print >>f, dummy_main_fn

####################################################################################################
# Test all binary operators.
####################################################################################################
for (op, name, signed) in binary_operators:
    with file('generated_tests/operator_%s.c' % name, 'w') as f:
        print >>f, tvc_args + ' --ret-unsigned'
        print >>f, 'unsigned f() {'
        print >>f, '  unsigned x = 1;'
        print >>f, '  unsigned y = 2;'
        print >>f, '  return x %s y;' % op
        print >>f, '}'
        print >>f, dummy_main_fn

    if signed:
        with file('generated_tests/operator_%s_signed.c' % name, 'w') as f:
            print >>f, tvc_args
            print >>f, 'signed f() {'
            print >>f, '  signed x = 1;'
            print >>f, '  signed y = 2;'
            print >>f, '  return x %s y;' % op
            print >>f, '}'
            print >>f, dummy_main_fn

####################################################################################################
# Test all unary operators.
####################################################################################################
for (op, name) in unary_operators:
    with file('generated_tests/operator_%s.c' % name, 'w') as f:
        print >>f, tvc_args + ' --ret-unsigned'
        print >>f, 'unsigned f() {'
        print >>f, '  unsigned x = 1;'
        print >>f, '  return %sx;' % op
        print >>f, '}'
        print >>f, dummy_main_fn

####################################################################################################
# Test all postfix operators.
####################################################################################################
for (op, name) in postfix_operators:
    with file('generated_tests/operator_%s.c' % name, 'w') as f:
        print >>f, tvc_args + ' --ret-unsigned'
        print >>f, 'unsigned f() {'
        print >>f, '  unsigned x = 1;'
        print >>f, '  return x%s;' % op
        print >>f, '}'
        print >>f, dummy_main_fn

####################################################################################################
# Test sizeof with all types.
####################################################################################################
for t in types:
    with file('generated_tests/sizeof_%s.c' % t.replace(' ', '_'), 'w') as f:
        print >>f, tvc_args
        print >>f, 'int f() {'
        print >>f, '  return sizeof (%s);' % t
        print >>f, '}'
        print >>f, dummy_main_fn

####################################################################################################
# Test _Alignof with all types.
####################################################################################################
#for t in types:
#    with file('generated_tests/alignof_%s.c' % t.replace(' ', '_'), 'w') as f:
#        print >>f, tvc_args
#        print >>f, 'int f() {'
#        print >>f, '  return _Alignof (%s);' % t
#        print >>f, '}'
#        print >>f, dummy_main_fn

####################################################################################################
# Test conversions between signed/unsigned types of the same size.
####################################################################################################
for t in base_types:
    with file('generated_tests/signed_unsigned_%s.c' % t.replace(' ', '_'), 'w') as f:
        print >>f, tvc_args + ' --ret-unsigned'
        print >>f, 'unsigned %s f() {' % t
        print >>f, '  unsigned %s x;' % t
        print >>f, '  signed %s y;' % t
        print >>f, '  x = 1;'
        print >>f, '  y = x;'
        print >>f, '  x = y;'
        print >>f, '  return x;'
        print >>f, '}'
        print >>f, dummy_main_fn

####################################################################################################
# Test conversions between types of different sizes.
####################################################################################################
for i, t1 in enumerate(base_types[:-1]):
    t2 = base_types[i + 1]
    for signed in ('signed', 'unsigned'):
        with file('generated_tests/ext_trunc_%s_%s_%s.c' % (signed, t1, t2.replace(' ', '_')), 'w') as f:
            print >>f, tvc_args + (' --ret-unsigned' if (signed == 'unsigned') else '')
            print >>f, '%s %s f() {' % (signed, t1)
            print >>f, '  %s %s x;' % (signed, t1)
            print >>f, '  %s %s y;' % (signed, t2)
            print >>f, '  x = 1;'
            print >>f, '  y = x;'
            print >>f, '  x = y;'
            print >>f, '  return x;'
            print >>f, '}'
            print >>f, dummy_main_fn
