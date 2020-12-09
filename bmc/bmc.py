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
   
    #choses and prepares initial state and property 
    initial = simplify(Not(prp)) if backward else simplify(init)
    negPrp = simplify(init) if backward else simplify(Not(prp))
    
    #set up variables for initial state
    currVals = []
    for i in range(len(xs)):
        currVals.append(Bool(chr( ord("a") + i) + str(k)))

    #substitute them
    for i in range(len(xs)):
        initial = substitute(initial, (xs[i], currVals[i]))
        negPrp = substitute(negPrp, (xs[i], currVals[i]))

    solver.add(initial)
    solver.push()    
    solver.add(negPrp)    
    
    #state bank for completness
    if completeness:
        states = []
        states.append(currVals)

    if (maxk == None):
        maxk = math.inf
    while (k < maxk):
        #setup new vars for next state
        nextVals = []
        for i in range(len(xs)):
            nextVals.append(Bool(chr( ord("a") + i) + str(k + 1)))
        
        #first checking without any transition
        if (solver.check() == sat):
            print("The property does not hold.")
            print(f"Finished with k={k}.")
            return False

        #remove negPrp constraint to substitute with next state vars 
        solver.pop()
        t = simplify(trans)
        negPrp = simplify(init) if backward else simplify(Not(prp))

        for i in range(len(xs)):
            if backward:
                #to revert direction
                t = substitute(t, (xs[i], nextVals[i]), (xns[i], currVals[i]))
                negPrp = substitute(negPrp, (xs[i], nextVals[i])) 
            else:
                t = substitute(t, (xs[i], currVals[i]), (xns[i], nextVals[i]))
                negPrp = substitute(negPrp, (xs[i], nextVals[i]))
        #this chcecks for appearence of the same state before
        if completeness:
            diff = False
            for state in states:
                b = True
                for i in range(len(state)):
                    b = And(b, (state[i] == nextVals[i]))
                diff = Or(diff, b)

                solver.add(Not(diff))
                if (solver.check() == unsat):
                    print("The property holds.")
                    print(f"Finished with k={k}.")
                    return 0
            states.append(nextVals)

        solver.push()
        solver.add(t)

        solver.push()
        solver.add(negPrp)

        currVals = nextVals
   
        k += 1

    if (solver.check() == unsat):
        print("Unknown.")
        print(f"Finished with k={k}.")
        return 1   
    print("The property holds.")
    print(f"Finished with k={k}.")
    return 0

if __name__ == "__main__":
    from sys import argv
    from os.path import isfile
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

