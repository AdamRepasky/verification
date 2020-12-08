#!/usr/bin/python

from z3 import And, Or, Not, Bool, BoolVal
from . parser import Parser

class Z3Parser(Parser):
    def createVariable(self, name):
        return Bool(name)

    def createAnd(self, *args):
        if len(args) == 0:
            return BoolVal(False)
        return And(*args)

    def createOr(self, *args):
        if len(args) == 0:
            return BoolVal(True)
        return Or(*args)

    def createNot(self, arg):
        return Not(arg)



