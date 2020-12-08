#!/usr/bin/python

from pysmt.shortcuts import Symbol, And, Or, Not, TRUE, FALSE
from . parser import Parser

class PySMTParser(Parser):
    def createVariable(self, name):
        return Symbol(name) # bool is the default

    def createAnd(self, *args):
        if len(args) == 0:
            return FALSE
        return And(*args)

    def createOr(self, *args):
        if len(args) == 0:
            return TRUE
        return Or(*args)

    def createNot(self, arg):
        return Not(arg)


