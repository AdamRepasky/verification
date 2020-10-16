#!/usr/bin/python3

from language import Instruction, Variable, Cmp
from interpreter import ExecutionState, Interpreter
from z3 import *

class SymbolicExecutionState(ExecutionState):
    def __init__(self, pc):
        super().__init__(pc)
       	
        solver = Solver()
        # add constraints here
        # dont forget to create _copy_ of attributes
        # when forking states (i.e., dont use
        # new.attr = old.attr, that would
        # only create a reference)

    def eval(self, v):
        if isinstance(v, bool):
            return Bool(v) # convert int to z3 BoolVal
        # NOTE: this must be before IntVal, since True/False
        # match also IntVal
        if isinstance(v, int):
            return Int(v) # convert int to z3 IntVal
        assert isinstance(v, Instruction)
        return self.values.get(v)
    def copy(self):
        # must be overriden for symbolic execution
        # if you add new attributes
        n = ExecutionState(self.pc)
        n.variables = self.variables.copy()
        n.values = self.values.copy()
        n.solver = self.solver.copy()
        n.error = self.error
        
        return n
    def read(self, var):
        assert isinstance(var, Variable)
        return self.variables.get(var)

    def write(self, var, value):
        assert isinstance(var, Variable)
        # in symbolic execution, value is expression, not int...
        assert isinstance(value, (ArithRef, BoolRef))
        self.variables[var] = value

    def set(self, lhs, val):
        assert isinstance(lhs, Instruction)
        # in symbolic execution, val is expression, not int...
        print(type(val))
        assert isinstance(val, (ArithRef, BoolRef))
        self.values[lhs] = val

class SymbolicExecutor(Interpreter):
    def __init__(self, program):
        super().__init__(program)
        self.executed_paths = 0
        self.errors = 0
        self.next_char = 96
    def getNextChar():
        self.next_char += 1
        return chr(self.next_char)
    def executeJump(self, state):
        jump = state.pc
        condval = state.eval(jump.get_condition())
        if condval is None:
            state.error = f"Using unknown value: {jump.get_condition()}"
            return state

        assert condval in [True, False], f"Invalid condition: {condval}"
        successorblock = jump.get_operand(0 if condval else 1)
        state.pc = successorblock[0]
        return state

    def executeMem(self, state):
        instruction = state.pc
        ty = instruction.get_ty()
        op = instruction.get_operand(0)
        if ty == Instruction.LOAD:
            value = state.read(op)
            if value is None:
                state.write(op, Int(self.getNextChar()))
                #state.error = f"Reading uninitialied variable: {op.get_name()}"
            state.set(instruction, value)
        elif ty == Instruction.STORE:
            value = state.eval(op)
            if value is None:
                state.error = f"Using unknown value: {op}"
            state.write(instruction.get_operand(1), value)
        else:
            raise RuntimeError(f"Invalid memory instruction: {instruction}")

        return state

    def executeArith(self, state):
        instruction = state.pc
        a = state.eval(instruction.get_operand(0))
        if a is None:
            state.error = f"Using unknown value: {instruction.get_operand(0)}"
            return state
        b = state.eval(instruction.get_operand(1))
        if b is None:
            state.error = f"Using unknown value: {instruction.get_operand(1)}"
            return state

        ty = instruction.get_ty()
        if ty == Instruction.ADD:
            result = a + b
        elif ty == Instruction.SUB:
            result = a - b
        if ty == Instruction.MUL:
            result = a * b
        if ty == Instruction.DIV:
            if b == 0:
                state.error = f"Division by 0: {instruction}"
                return state
            result = a / b

        state.set(instruction, result)

        return state

    def executePrint(self, state):
        instruction = state.pc

        vals = []
        for op in instruction.get_operands():
            val = state.eval(op)
            if val is None:
                state.error = f"Using unknown value: {op}"
                break

            vals.append(val)

        if vals:
            print(" ".join(map(str, vals)))

        return state

    def executeCmp(self, state):
        cmpinst = state.pc
        predicate = cmpinst.get_predicate()
        a = state.eval(cmpinst.get_operand(0))
        if a is None:
            state.error = f"Using unknown value: {cmpinst.get_operand(0)}"
            return state
        b = state.eval(cmpinst.get_operand(1))
        if b is None:
            state.error = f"Using unknown value: {cmpinst.get_operand(1)}"
            return state

        if predicate == Cmp.LT:
            result = a < b
        elif predicate == Cmp.LE:
            result = a <= b
        elif predicate == Cmp.GT:
            result = a > b
        elif predicate == Cmp.GE:
            result = a >= b
        elif predicate == Cmp.EQ:
            result = a == b
        elif predicate == Cmp.NE:
            result = a != b
        else:
            raise RuntimeError(f"Invalid comparison: {cmpinst}")

        state.set(cmpinst, result)

        return state

    def executeAssert(self, state):
        instruction = state.pc
        condval = state.eval(instruction.get_condition())
        if condval is None:
            state.error = f"Using unknown value: {jump.get_condition()}"
            return state

        assert condval in [True, False], f"Invalid condition: {condval}"
        if condval is False:
            state.error = f"Assertion failed: {instruction}"
        return state

    def executeInstruction(self, state):
        instruction = state.pc
        ty = instruction.get_ty()
        # print('executing:', instruction)

        if ty == Instruction.JUMP:
            return self.executeJump(state)

        if ty in [Instruction.ADD, Instruction.SUB,
                  Instruction.MUL, Instruction.DIV]:
            state =  self.executeArith(state)
        elif ty in [Instruction.LOAD, Instruction.STORE]:
            state = self.executeMem(state)
        elif ty == Instruction.CMP:
            state = self.executeCmp(state)
        elif ty == Instruction.PRINT:
            state = self.executePrint(state)
        elif ty == Instruction.HALT:
            return None # kill the execution
        elif ty == Instruction.ASSERT:
            state = self.executeAssert(state)
        else:
            raise RuntimeError(f"Unimplemented instruction: {instruction}")

        if not state.error:
            state.pc = state.pc.get_next_inst()
            if not state.pc:
                return None

        return state

    def run(self):
        entryblock = program.get_entry()
        state = SymbolicExecutionState(entryblock[0])

        while state:
            state = self.executeInstruction(state)
            if state and state.error:
                #TODO pop last constraint and continue in other branch maybe increase execued_paths too
                state.error = None
                self.errors += 1

        #TODO?

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
