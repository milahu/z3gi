from z3gi.model import Transition, Acceptor
from abc import ABCMeta, abstractmethod

class RegisterAutomaton(Acceptor):
   def __init__(self, locations, loc_to_acc, loc_to_trans, registers):
      super.__init__(locations, loc_to_trans, loc_to_acc)
      self.register = registers

class RATransition(Transition):
    def __init__(self, start_state, start_label, guard, assignment, end_state):
        Transition.__init__(start_state, start_label, end_state)
        self.guard = guard
        self.assignment = assignment

    def is_enabled(self, action, valuation):
        if action.label == self.start_label:
            satisfied = self.guard.is_satisfied(action.value, valuation)
            return satisfied
        return False



class Guard(metaclass=ABCMeta):
    def __init__(self):
        pass

    @abstractmethod
    def is_satisfied(self, valuation, value):
        pass

class RegisterGuard(Guard):
    def __init__(self, register):
        super.__init__()
        self.register = register

    def is_satisfied(self, valuation, value):
        return valuation[self.register] == value

class FreshGuard(Guard):
    def __init__(self, guarded_registers = []):
        super.__init__()
        self.registers = guarded_registers

    def is_satisfied(self, valuation, value):
        for register in self.registers:
            if valuation[register] == value:
                return False
        return True

class Assignment(metaclass=ABCMeta):
    def __init__(self):
        pass

    @abstractmethod
    def update(self, valuation, value):
        pass


class RegisterAssignment(Assignment):
    def __init__(self, register):
        super.__init__()
        self.register = register

    def update(self, valuation, value):
        valuation[self.register] = value

class NoAssignment(Assignment):
    def __init__(self):
        super.__init__()
    def update(self, valuation):
        return valuation