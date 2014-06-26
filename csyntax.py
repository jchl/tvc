base_types = [
    'char',
    'short',
    'int',
    'long',
    'long long' ]

types = ['char'] + ['%s %s' % (signed, t)
                    for signed in ('signed', 'unsigned')
                    for t in base_types]

binary_operators = [
    ('+', 'plus', False),
    ('-', 'minus', False),
    ('*', 'times', False),
    ('/', 'divide', True),
    ('%', 'mod', True),
# clang compiles && and || to code involving branches
#    ('&&', 'and', False),
#    ('||', 'or', False),
    ('&', 'bitand', False),
    ('|', 'bitor', False),
    ('^', 'bitxor', False),
    ('<<', 'shiftleft', False),
    ('>>', 'shiftright', False),
    (',', 'comma', False),
    ('<', 'lt', True),
    ('<=', 'leq', True),
    ('==', 'eq', False),
    ('!=', 'neq', False),
    ('>=', 'geq', True),
    ('>', 'gt', True),
]

unary_operators = [
    ('+', 'uplus'),
    ('-', 'uminus'),
# not triggers a crash (issue #29) in csem
#    ('!', 'not'),
    ('~', 'bitnot'),
# pre-increment and pre-decrement get translated to compound assignment, which still isn't supported
# by csem
#    ('++', 'preincr'),
#    ('--', 'predecr'),
]

postfix_operators = [
# post-increment and post-decrement get stuck during csem reduction
#    ('++', 'postincr'),
#    ('--', 'postdecr'),
]

dummy_main_fn = '''
// This is here just to keep csem happy.
int main() {
  return 0;
}
'''
