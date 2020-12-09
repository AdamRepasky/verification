#!/usr/bin/python

from bmcparsers.cmdparser import parse_cmd

# Choose which package you want to use: Z3 or pySMT
## --
from bmcparsers.z3parser import Z3Parser
from z3 import *
#from bmcparsers.pysmtparser import PySMTParser
#from pysmt.shortcuts import *
from math import inf

def bmc(maxk, xs, xns, prp, init, trans, backward = False, completeness = False):
    """
    Bounded model checking

    \param maxk           the upper bound on the number of iterations (path
                          length)
    \param xs             variables used in formulas
    \param xns            next-state variables used in formulas.
                          For a variable xs[i], the next-state variable is
                          xns[i].
    \param prp            property formula
    \param init           init relation formula
    \param trans          transition relation formula
    \param backward       set to True to perform the backward check
    \param completeness   set to True to perform completeness check
    """


    k = 0

    queue = []
    queue.append(init)

    solver = Solver()
    solver.push()
    
    
    # Implement the BMC algorithm here
    print(maxk, xs, xns, prp, init, trans, backward, completeness)
    if (maxk == None):
        maxk = math.inf
    while (k < maxk):

        t = queue.pop(0)
        for transition in trans:
            t = And(t, transition)
            solver.push()
            solver.add(t)
            print(solver)
            queue.append(t)
            solver.pop()
            
        k += 1
        
    
    print(f"Finished with k={k}.")
    return True

if __name__ == "__main__":
    from sys import argv
    from os.path import isfile
    print("hello")
    args = parse_cmd()
    parser = Z3Parser()
    #parser = PySMTParser()

    maxk = args.maxk
    V, init, trans = parser.parseSystem(args.vars, args.init, args.trans)
    prp = parser.parseFormula(args.prp, V)

    print(
"""
Max k:                 {0}
Variables:             {1}
Next-state variables:  {2}
Init relation:
{3}
Transition relation:
{4}
Property:
{5}
Check completeness: {6}
Check backwards: {7}
""".format(maxk, ",".join(map(str, V.xs)), ",".join(map(str, V.xns)),
           str(init), str(trans), str(prp), args.completeness, args.backward)
)

    if init is None or trans is None:
        assert False, "Parsing the formulas failed"

    if args.dot is not None:
        from bmcparsers.dot import todot
        todot(args.dot, V, init, trans, prp)

    ###
    # Perform BMC
    ###
    print('--------------------------------')
    print('Running BMC')
    res = bmc(maxk, V.xs, V.xns, prp, init, trans, args.backward, args.completeness)

    exit(0 if res == True else 1)

