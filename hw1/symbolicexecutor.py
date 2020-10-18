#!/usr/bin/python3

from language import Instruction, Variable, Cmp
from interpreter import ExecutionState, Interpreter
from z3 import *

class SymbolicExecutionState(ExecutionState):
    def __init__(self, pc):
        super().__init__(pc)
       	
        self.constraints = []
        #self.solver = Solver()
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
    def copy(self):
        # must be overriden for symbolic execution
        # if you add new attributes
        n = SymbolicExecutionState(self.pc)
        n.variables = self.variables.copy()
        n.values = self.values.copy()
        #n.solver = self.solver.copy()
        n.constraints = self.constraints.copy()
        n.error = self.error
        
        return n
    def read(self, var):
        assert isinstance(var, Variable)
        return self.variables.get(var)

    def write(self, var, value):
        ##print(var, value)
        assert isinstance(var, Variable)
        # in symbolic execution, value is expression, not int...
        assert isinstance(value, (ArithRef, IntNumRef, BoolRef))
        self.variables[var] = value

    def set(self, lhs, val):
        assert isinstance(lhs, Instruction)
        # in symbolic execution, val is expression, not int...
        #print(type(val))
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
        self.next_char = 96
        self.solver = Solver()
        self.stateStack = []
        self.branchSelected = False 
    def getNextChar(self):
        self.next_char += 1
        return chr(self.next_char)

    def executeJump(self, state):
        ##print(state.variables, state.values)
        jump = state.pc
        condval = state.eval(jump.get_condition())
        ##print(condval)
        ##print(type(condval))
        ##print(jump)
        if condval is None:
            state.error = f"Using unknown value: {jump.get_condition()}"
            return state
        assert isinstance(condval, (BoolRef, True, False))
        #assert condval in [True, False, BoolRef], f"Invalid condition: {condval}"
        
        if isinstance(condval, BoolRef):
            #here we need to maxe branching
            #first make copy of current state for other branch
            otherState = state.copy()
            ###print("jump states ", state, otherState)
            #add new constraint
            state.constraints.append(condval)
            #state.solver.add(condval)
            
            #push negated constraint into other branch state
            otherState.constraints.append(Not(condval))
            ###print("constraints1 ", state.constraints)
            ###print("constraints2 ", otherState.constraints)
            #otherState.add(Not(condval))
            #
            #bool a,b = False, False
            self.stateStack.append((state, 0))
            self.stateStack.append((otherState, 1))
            #if (state.check() == sat):
            #    #a = True
            #    successorblock = jump.get_operand(0)
            #    state.pc = successorblock[0]
            #    self.stateStack.append(state)
            #if (otherState.check() == sat):
            #    #b = True
            #    successorblock = jump.get_operand(1)
            #    otherState.pc = successorblock[0]
            #    self.stateStack.append(otherState)
            #self.stateStack.append(Not(condval))
            #self.solver.add(Not(condval))
            #print(self.solver)
        #successorblock = jump.get_operand(0 if condval else 1)

        #state.pc = successorblock[0]
        self.branchSelected = False
        return None

    def executeMem(self, state):
        instruction = state.pc
        ty = instruction.get_ty()
        op = instruction.get_operand(0)
        if ty == Instruction.LOAD:
            value = state.read(op)
            if value is None:
                value = Int(self.getNextChar())
                state.write(op, value)
                #print(op, op.get_name(), value)
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
            ##print(b)
            if b == Int(0):
                ##print("okay")
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

        #if vals:
            #print(" ".join(map(str, vals)))
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
        assert isinstance(condval, (BoolRef, bool))
        #print("assert condval =", condval, type(condval))
        #assert condval in [True, False], f"Invalid condition: {condval}"
        if condval == False:
            #print("assert False")
            state.error = f"Assertion failed: {instruction}"
            return state
        #TODO it should branch depending on satisfiability of condval
        #if condval is False:
        #    state.error = f"Assertion failed: {instruction}"
        if condval == True:
            #print("assert True")
            return state
        #print("assert symbolic")

        negState = state.copy()
        negState.constraints.append(Not(condval))
        self.solver.reset()
        self.solver.push()
        for c in negState.constraints:
            self.solver.add(c)
        if (self.solver.check() == sat):
            #print("its unsat")
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
            #state.pc = state.pc.get_next_inst()
            #if not state.pc:
            #    return None
        return state
        
        #print(condval)
        #print(type(condval))
        #otherState = state.copy()
        #add new constraint
        #state.constraints.append(condval)
        #push negated constraint into other branch state
        #otherState.constraints.append(Not(condval))
        #self.stateStack.append((state, None)) #maybe one should be enough and let this function handle it (either one branch continues (constraints remain) and one ends here, or both end here (only one error); if both continue we make two separate branches (probably))
        #self.stateStack.append((otherState, None))

        #self.branchSelected = False
        return None

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
        #print(len(self.stateStack))
        self.solver.reset()
        pop = self.stateStack.pop() #maybe add another assert to this state(but eror shouldn't happen here; no instruction is executed here)
        #print("pop ", pop)
        state = pop[0]
        #if pop[1] == None:
        #    self.solver.push()
        #    for c in state.constraints:
        #        self.solver.add(c)
        #    #print("solver ", self.solver)
        #    if (self.solver.check() == unsat):
        #        print("its unsat")
        #        state.error = "Assertion unsat"
        #        self.branchSelected = True
        #        return state
        #        #we found new reachable branch TODO check whether this is ok, probably its ok ONLY if all branches created are leaves! (check HALT too)
        #    else:
        #        print("its sat")
        #        self.branchSelected = True
        #        state.pc = state.pc.get_next_inst()
        #        if not state.pc:
        #            return None
        #        return state
        #
        #
        #else:
        jump = state.pc
        successorblock = jump.get_operand(pop[1])
        self.solver.push()
        for c in state.constraints:
            self.solver.add(c)
        #print("solver ", self.solver)
        if (self.solver.check() == sat):
            state.pc = successorblock[0]
            self.branchSelected = True
            #we found new reachable branch TODO check whether this is ok, probably its ok ONLY if all branches created are leaves! (check HALT too)
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
                #print("after execution in error")
                #TODO pop last constraint and continue in other branch maybe increase execued_paths too
                #state.error = None
                self.errors += 1
                self.executed_paths += 1
                state = None
                self.branchSelected = False
            if state == None and self.branchSelected:
                #print("after execution in finished")
                self.branchSelected = False
                self.executed_paths += 1

                while (state == None and len(self.stateStack) > 0):
                    state = self.popNextSatState()

            elif state == None and not self.branchSelected and len(self.stateStack) > 0:
                #print("after execution in branching point")
                while (state == None and len(self.stateStack) > 0):
                    state = self.popNextSatState()
            #if state == "branch":
            #    break;
            #state = self.executeInstruction(state)
            #if state == "branch":
            #    continue;
            #if state and state.error:
            #    #TODO pop last constraint and continue in other branch maybe increase execued_paths too
            #    #state.error = None
            #    self.errors += 1
            #    #self.executed_paths += 1
            #    state = None
            #if state == None and self.branchSelected:
            #    state = self.popNextSatState()
            #    self.executed_paths += 1
                        
            #if state and state.error:
            #    #TODO pop last constraint and continue in other branch maybe increase execued_paths too
            #    #state.error = None
            #    self.errors += 1
            #    #self.executed_paths += 1
            #    state = None

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
