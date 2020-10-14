#!/usr/bin/python3

from language import Instruction, Variable, Cmp
from interpreter import ExecutionState, Interpreter
from z3 import *

class SymbolicExecutionState(ExecutionState):
    def __init__(self, pc):
        super().__init__(pc)

        # add constraints here

        # dont forget to create _copy_ of attributes
        # when forking states (i.e., dont use
        # new.attr = old.attr, that would
        # only create a reference)

    def eval(self, v):
        if isinstance(v, bool):
            return BoolVal(v) # convert int to z3 BoolVal
        # NOTE: this must be before IntVal, since True/False
        # match also IntVal
        if isinstance(v, int):
            return IntVal(v) # convert int to z3 IntVal
        assert isinstance(v, Instruction)
        return self.values.get(v)

class SymbolicExecutor(Interpreter):
    def __init__(self, program):
        super().__init__(program)

    def run(self):
        entryblock = program.get_entry()
        state = SymbolicExecutionState(entryblock[0])

        pass
        #TODO

        print(f"Executed paths: {self.executed_paths}")
        print(f"Error paths: {self.errors}")

if __name__ == "__main__":
    from parser import Parser
    from sys import argv
    if len(argv) != 2:
        print(f"Wrong numer of arguments, usage: {argv[0]} <program>")
        exit(1)
    parser = Parser(argv[1])
    program = parser.parse()
    if program is None:
        print("Program parsing failed!")
        exit(1)

    I = SymbolicExecutor(program)
    exit(I.run())
