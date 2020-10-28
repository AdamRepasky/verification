#!/usr/bin/python3

from language import Instruction, Variable, Cmp
from interpreter import ExecutionState, Interpreter
from z3 import *

# each branch of symbolic execution has its own SymbolicExecutionState
# object with assigned constraints 
class SymbolicExecutionState(ExecutionState):
    def __init__(self, pc):
        super().__init__(pc)
       	
        #constraints collection 
        self.constraints = []

    def eval(self, v):
        if isinstance(v, bool):
            return BoolVal(v) # convert int to z3 BoolVal
        # NOTE: this must be before IntVal, since True/False
        # match also IntVal
        if isinstance(v, int):
            return IntVal(v) # convert int to z3 IntVal
        assert isinstance(v, Instruction)
        return self.values.get(v)
    def copy(self):
        n = SymbolicExecutionState(self.pc)
        n.variables = self.variables.copy()
        n.values = self.values.copy()

        n.constraints = self.constraints.copy()
        n.error = self.error
        
        return n

    def write(self, var, value):
        assert isinstance(var, Variable)
        # in symbolic execution, value is expression, not int...
        assert isinstance(value, (ArithRef, IntNumRef, BoolRef))
        self.variables[var] = value

    def set(self, lhs, val):
        assert isinstance(lhs, Instruction)
        # in symbolic execution, val is expression, not int...
        assert isinstance(val, (ArithRef, IntNumRef, BoolRef))
        self.values[lhs] = val

    def __repr__(self):
        variables = {x.get_name() : v for (x, v) in self.variables.items()}
        values = {x.get_name() : v for (x, v) in self.values.items()}
        return f"[\n"\
               f"pc: {self.pc}\n"\
               f"variables: {variables}\n"\
               f"values: {values}\n"\
               f"constraints: {self.constraints}\n"\
                "]"

class SymbolicExecutor(Interpreter):
    def __init__(self, program):
        super().__init__(program)
        self.executed_paths = 0
        self.errors = 0
        self.next_char = 96 #idk about this for sure
        self.solver = Solver()

        #states waiting to be executed
        self.stateStack = []
        self.branchSelected = False 

    def executeJump(self, state):
        jump = state.pc
        condval = state.eval(jump.get_condition())

        if condval is None:
            state.error = f"Using unknown value: {jump.get_condition()}"
            return state
        assert isinstance(condval, (BoolRef, True, False))
        
        if isinstance(condval, BoolRef):
            # here branching happens
            # first make copy of current state for other branch
            otherState = state.copy()
            # add new constraint to first branch state
            state.constraints.append(condval)
            
            # push negated constraint into other branch state
            otherState.constraints.append(Not(condval))

            # add states to stack; second member of tuple describes which block of jump
            # will be accessed if constraints of state are satisfiable
            self.stateStack.append((state, 0))
            self.stateStack.append((otherState, 1))
        self.branchSelected = False
        return None

    def executeMem(self, state):
        instruction = state.pc
        ty = instruction.get_ty()
        op = instruction.get_operand(0)
        if ty == Instruction.LOAD:
            value = state.read(op)
            if value is None:
                value = Int("x")
                state.write(op, value)
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
        #did not do branching here since it was stated it is not necessary for this homework
            if b == Int(0):
                state.error = f"Division by 0: {instruction}"
                return state
            result = a / b

        state.set(instruction, result)

        return state

    #overridden to not print, just check values
    def executePrint(self, state):
        instruction = state.pc

        for op in instruction.get_operands():
            val = state.eval(op)
            if val is None:
                state.error = f"Using unknown value: {op}"
                break
        return state

    def executeAssert(self, state):
        instruction = state.pc
        condval = state.eval(instruction.get_condition())
        if condval is None:
            state.error = f"Using unknown value: {jump.get_condition()}"
            return state
        assert isinstance(condval, (BoolRef, bool))

        if condval == False:
            state.error = f"Assertion failed: {instruction}"
            return state
        if condval == True:
            return state
        #if condval is symbolic
        
        # braching happens here too but its not like in executeJump since
        # only one of paths (constraints + assert constraint is sat) can continue
        # other one (constraints + negation of assert constraint is sat) can not (raise error but counts as a path)
        # its solved inside this function since we do not need to add anything to stack
        negState = state.copy()
        negState.constraints.append(Not(condval))
        self.solver.reset()
        self.solver.push()
        for c in negState.constraints:
            self.solver.add(c)
        if (self.solver.check() == sat):
            negState.error = "err"
            self.errors += 1
            self.executed_paths += 1 

        state.constraints.append(condval)
        self.solver.reset()
        self.solver.push()
        for c in state.constraints:
            self.solver.add(c)
        if (self.solver.check() == unsat):
            state.error = "unsat expression"
        return state

    def executeInstruction(self, state):
        instruction = state.pc
        ty = instruction.get_ty()
        #print('executing:', instruction)

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
            state =  self.executeAssert(state)
        else:
            raise RuntimeError(f"Unimplemented instruction: {instruction}")

        if not state.error:
            state.pc = state.pc.get_next_inst()
            if not state.pc:
                return None

        return state

    def popNextSatState(self):
        self.solver.reset()
        pop = self.stateStack.pop()
        state = pop[0]
        jump = state.pc
        successorblock = jump.get_operand(pop[1])
        self.solver.push()
        for c in state.constraints:
            self.solver.add(c)

        if (self.solver.check() == sat):
            state.pc = successorblock[0]
            self.branchSelected = True
        else:
            state = None
            self.branchSelected = False
        return state

    def run(self):
        entryblock = program.get_entry()
        state = SymbolicExecutionState(entryblock[0])
        self.branchSelected = True
        
        while state:
            if state and not state.error:
                state = self.executeInstruction(state)
            if state and state.error:
                self.errors += 1
                self.executed_paths += 1
                state = None
                self.branchSelected = False
            if state == None and self.branchSelected:
                self.branchSelected = False
                self.executed_paths += 1

                while (state == None and len(self.stateStack) > 0):
                    state = self.popNextSatState()

            elif state == None and not self.branchSelected and len(self.stateStack) > 0:
                while (state == None and len(self.stateStack) > 0):
                    state = self.popNextSatState()

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
