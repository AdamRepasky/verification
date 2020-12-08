#!/usr/bin/python

#from pysmt.shortcuts import *
from z3 import *

def _getState(n, V, nextState = False):
    vals=[]
    i = 0

    if nextState:
        variables = V.xns
    else:
        variables = V.xs

    for x in variables:
        if n & (1 << i):
            vals.append(x)
        else:
            vals.append(Not(x))

        i += 1

    return And(vals)

def _getStateName(n, V):
    name = ''
    i = 0
    for x in V.xs:
        if i > 0:
            name += ' '

        if n & (1 << i):
            name += str(x)
        else:
            name += '!{0}'.format(str(x))

        i += 1

    return name

def _stateSat(n, V, F):
    # we could use the sat solver here instead
    s = Solver()
    return s.check(And(F, _getState(n, V))) == sat

def _satTrans(n1, n2, V, F):
    s = Solver()
    return s.check(And(F, _getState(n1, V), _getState(n2, V, True))) == sat

def _todot(f, V, init, trans, prp):
    "We associate a number to each state -\
     the bits are the valuation of variables"

    f.write("digraph S {\n")
    # dump nodes
    for n in range(0, 2**len(V.xs)):
        node=\
        '  NODE{0}[label="{1}" {2} {3}]\n'.format(n, _getStateName(n, V),
                                                 "shape=doublecircle"\
                                                        if _stateSat(n, V, init)
                                                        else "",
                                                 "color=red" if not _stateSat(n, V, prp)
                                                             else "")
        f.write(node)


    # dump edges
    f.write('\n')
    for n1 in range(0, 2**len(V.xs)):
        for n2 in range(0, 2**len(V.xs)):
            if (_satTrans(n1, n2, V, trans)):
                f.write("NODE{0} -> NODE{1}\n".format(n1, n2))

    f.write("\n}\n")

def todot(path, V, init, trans, prp):
    """
    Dump the given system into a .dot file 'path'

    V     - variables
    init  - initial formula
    trans - transition formula
    prp   - property formula
    """

    with open(path, 'wt') as f:
        _todot(f, V, init, trans, prp)

