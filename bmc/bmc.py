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

    solver = Solver()
    solver.push()
    solver.add(simplify(init))
    solver.push()
    
    negPrp = simplify(Not(prp))
    solver.add(negPrp)    

    t = trans
    
    # Implement the BMC algorithm here

    if (maxk == None):
        maxk = math.inf
    while (k < maxk):
        
        #solver.push()
        #solver.add(simplify(t))
        if completeness:
            pass
            #for i in range(len(xs)):
            #    solver.add(xns[i] != xs[i])
        #print(simplify(Not(And(Or(Bool('x'))))))
        print(solver)
        print(solver.check())
        if (solver.check() == sat):
            print("The property does not hold.")
            print(f"Finished with k={k}.")
            return False
        print("pop: ", solver.pop())
        solver.push()
        solver.add(simplify(t))

        for i in range(len(xs)):  
            s = substitute(t, (xns[i], xs[i]), (xs[i], xns[i]))
            if completeness:
                constraints = solver.assertions()
                #constraints = simplify(constraints)
                print(type(constraints))
                print("c:", constraints, "ns: ", solver.assertions())
                print("t: ", t)
                print("s: ", s)
                if s == t:
                    print("The property holds.")
                    print(f"Finished with k={k}.")
                    return True
            t = s
            negPrp = substitute(negPrp, (xns[i], xs[i]), (xs[i], xns[i]))
        solver.push()
        solver.add(negPrp)
   
        k += 1
    if (solver.check() == unsat):
        print("Unknown.")
    else:    
        print("The property holds.")
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

