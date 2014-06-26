#!/usr/bin/env python

import sys
import random
from csyntax import *

# Large integer literals trigger a crash (issue #36) in csem
min_literal = -(2 ** 14) + 1
max_literal = (2 ** 14) - 1

def random_literal():
    n = random.randint(min_literal, max_literal)
    r = random.random()
    if r < 0.1:
        return hex(n)
    elif r < 0.2:
        return oct(n)
    else:
        return str(n)

def random_type():
    return random.choice(types)

def random_unary_operator():
    return random.choice(unary_operators)[0]

def random_postfix_operator():
    return random.choice(postfix_operators)[0]

def random_binary_operator():
    return random.choice(binary_operators)[0]

def random_cast():
    return '(%s)' % random_type()

def build_exp(vs, n):
    if n == 0:
        r = random.random()
        if r < 0.5:
            return random.choice(vs)
        elif r < 0.95:
            return random_literal()
# clang doesn't support _Alignof (or -std=c11)
#        elif r < 0.95:
#            return "(_Alignof (%s))" % random_type()
        else:
            return "(sizeof (%s))" % random_type()
    else:
        if random.random() < 0.1:
            r = random.random()
            if r < 0.3:
                uop = random_cast()
#            elif r < 0.6:
#                uop = random_postfix_operator()
            elif r < 0.95:
                uop = random_unary_operator()
# clang doesn't support _Alignof (or -std=c11)
#            elif r < 0.975:
#                uop = "_Alignof"
            else:
                uop = "sizeof"
            return '(%s %s)' % (uop, build_exp(vs, n - 1))
        elif random.random() < 0.1:
            return '(%s ? %s : %s)' % (build_exp(vs, n - 1), random_literal(), random_literal())
        else:
            bop = random_binary_operator()
            n1 = random.randint(0, n - 1)
            n2 = n - 1 - n1
            return '(%s %s %s)' % (build_exp(vs, n1), bop, build_exp(vs, n2))

def gen_file(f, nargs, nlcls, nops):
    return_type = random_type()
    print >>f, "// tvc-args: --main f" + (" --ret-unsigned" if "unsigned" in return_type else "")
    print >>f, dummy_main_fn
    args = ['a%d' % i for i in range(nargs)]
    print >>f, "%s f(%s) {" % (return_type, ", ".join("%s %s" % (random_type(), v) for v in args))
    lcls = ['x%d' % i for i in range(nlcls)]
    for v in lcls:
        print >>f, "    %s %s = %s;" % (random_type(), v, random_literal())
    while nops > 0:
        n = random.randint(0, nops)
        nops -= n
        print >>f, "    %s = %s;" % (random.choice(lcls), build_exp(lcls, n))
    print >>f, "    return %s;" % random.choice(lcls)
    print >>f, "}"

def main(argv):
    [_, filename, nargs, nlcls, nops] = argv
    with file(filename, 'w') as f:
        gen_file(f, int(nargs), int(nlcls), int(nops))

main(sys.argv)
