from z3gi.model import Transition, Acceptor, NoTransitionFired, MultipleTransitionsFired
from abc import ABCMeta, abstractmethod
import itertools
import collections
from typing import List

Action = collections.namedtuple('Action', ('label', 'value'))


class RATransition(Transition):
    def __init__(self, start_state, start_label, guard, assignment, end_state):
        super().__init__(start_state, start_label, end_state)
        self.guard = guard
        self.assignment = assignment

    def is_enabled(self, action, valuation):
        if action.label is self.start_label:
            satisfied = self.guard.is_satisfied(action.value, valuation)
            return satisfied
        return False

    def update(self, action, valuation):
        return self.assignment.update(valuation, action.value)

    def __str__(self, shortened = False):
        if not shortened:
            return "{0} {1}({2}) -> {3} {4}".format(self.start_state, self.start_label, self.guard,
                                               self.assignment, self.end_state)
        else:
            return "{0}({1}) -> {2} {3}".format(self.start_label, self.guard,
                                                    self.assignment, self.end_state)

class SymbolicValue(metaclass=ABCMeta):
    """Symbolic values can be used to symbolically express registers, constants and parameters."""
    def __init__(self, index):
        super().__init__()
        self.index = index

class Register(SymbolicValue):
    def __init__(self, index):
        super().__init__(index)

    def __str__(self):
        return "r" + str(self.index)


class RegisterAutomaton(Acceptor):
    def __init__(self, locations, loc_to_acc, loc_to_trans, registers):
      super().__init__(locations, loc_to_trans, loc_to_acc)
      self._registers = registers

    def registers(self) -> List[Register]:
        return self._registers

    def transitions(self, state: str, label:str = None) -> List[RATransition]:
        return super().transitions(state, label)

    def state(self, trace: List[Action]) -> str:
        init = -1
        reg_val = dict()
        for reg in self.registers():
            reg_val[reg] = init

        crt_state = self.start_state()
        for action in trace:
            transitions = self.transitions(crt_state, action.label)
            fired_transitions = [trans for trans in transitions if trans.is_enabled(action, reg_val)]

            # the number of fired transitions can be more than one since we could have multiple equalities
            # todo (merge into or guard?)
            if len(fired_transitions) == 0:
                raise NoTransitionFired

            if len(fired_transitions) > 1:
                raise MultipleTransitionsFired

            fired_transition = fired_transitions[0]
            reg_val = fired_transition.update(reg_val, action)
            crt_state = fired_transition.end_state

        return crt_state

class MutableRegisterAutomaton(RegisterAutomaton):
    def __init__(self):
        super().__init__([], dict(), dict(), [])

    def add_state(self, state, accepts):
        if state not in self._states:
            self._states.append(state)
        self._state_to_acc[state] = accepts


    def add_transition(self, state, transition):
        if state not in self._state_to_trans:
            self._state_to_trans[state]=[]
        self._state_to_trans[state].append(transition)
        for reg in transition.guard.registers():
            if reg not in self._registers:
                self._registers.append(reg)

    def to_immutable(self) -> RegisterAutomaton:
        return RegisterAutomaton(self._states, self._state_to_acc, self._state_to_trans, self._registers)

class Guard(metaclass=ABCMeta):
    """A guard with is_satisfied implements a predicate over the current register valuation and the parameter value. """
    def __init__(self):
        pass


    @abstractmethod
    def registers(self):
        """Returns the registers/constants over which the guard is formed"""
        pass

    # to make this more abstract, value would have to be replaced by param valuation
    @abstractmethod
    def is_satisfied(self, valuation, value):
        pass

class EqualityGuard(Guard):
    """An equality guard holds iff. the parameter value is equal to the value assigned to its register."""
    def __init__(self, register):
        super().__init__()
        self._register = register

    def is_satisfied(self, valuation, value):
        return valuation[self._register] == value

    def registers(self):
        return [self._register]

    def __str__(self):
        return "p=={0}".format(str(self._register))

class OrGuard(Guard):
    def __init__(self, guards):
        self.guards = guards

    def is_satisfied(self, valuation, value):
        for guard in self.guards:
            if guard.is_satisfied(valuation, value):
                return True
        return False

    def registers(self):
        regs_of_guards = [guard.registers() for guard in self.guards]
        regs = itertools.chain.from_iterable(regs_of_guards)
        seen = set()
        distinct_regs = [x for x in regs if x not in seen and not seen.add(x)]
        return list(distinct_regs)

    def __str__(self):
        all_guards = [str(guard) for guard in self.guards]
        return " \\/ ".join(all_guards)


class FreshGuard(Guard):
    """An fresh guard holds if the parameter value is different from the value assigned to any of its registers."""
    def __init__(self, guarded_registers = []):
        super().__init__()
        self._registers = guarded_registers

    def is_satisfied(self, valuation, value):
        for register in self._registers:
            if valuation[register] == value:
                return False
        return True

    def registers(self):
        return self._registers

    def __str__(self):
        if len(self._registers) == 0:
            return "True"
        else:
            all_deq = ["p!={0}".format(str(reg)) for reg in self._registers]
            return " /\\ ".join(all_deq)

class Assignment(metaclass=ABCMeta):
    """An assignment updates the valuation of registers using the old valuation and the current parameter value"""
    def __init__(self):
        pass

    # to make this more general, value would have to be replaced by variable(reg/param) mapping and par valuation
    @abstractmethod
    def update(self, valuation, value):
        pass


class RegisterAssignment(Assignment):
    def __init__(self, register):
        super().__init__()
        self.register = register

    def update(self, valuation, value):
        new_valuation = dict(valuation)
        new_valuation[self.register] = value
        return new_valuation

    def __str__(self):
        return "{0}:=p".format(str(self.register))


class NoAssignment(Assignment):
    def __init__(self):
        super().__init__()

    def update(self, valuation):
        return dict(valuation)

    def __str__(self):
        return "r:=r"

