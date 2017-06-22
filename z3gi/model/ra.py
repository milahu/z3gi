from z3gi.model import Transition, Acceptor, NoTransitionFired, NonDeterminism
from abc import ABCMeta, abstractmethod

class RegisterAutomaton(Acceptor):
    def __init__(self, locations, loc_to_acc, loc_to_trans, registers):
      super.__init__(locations, loc_to_trans, loc_to_acc)
      self.register = registers

    def state(self, trace):
        init = -1
        reg_val = dict()
        for reg in self.ra.get_registers():
            reg_val[reg] = init

        crt_state = self.start_state()
        for action in trace:
            transitions = self.transitions(crt_state, action.label)
            fired_transitions = [trans for trans in transitions if trans.is_enabled(action, reg_val)]

            # the number of fired transitions can be more than one since we could have multiple equalities
            # todo (merge into or guard?)
            if len(fired_transitions) == 0:
                raise NoTransitionFired

            fired_transition = fired_transitions[0]
            reg_val = fired_transition.update(reg_val, action)
            crt_state = fired_transition.end_state

        return crt_state

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

    def update(self, action, valuation):
        return self.assignment.update(valuation, action.value)


class Guard(metaclass=ABCMeta):
    def __init__(self):
        pass

    # to make this more abstract, value would have to be replaced by param valuation
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

    # to make this more general, value would have to be replaced by variable(reg/param) mapping and par valuation
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