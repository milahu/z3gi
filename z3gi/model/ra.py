from z3gi.model import Transition, Acceptor, NoTransitionFired, MultipleTransitionsFired, Transducer, \
    MutableAcceptorMixin, MutableAutomatonMixin
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

    def is_enabled(self, valuation, action):
        if action.label == self.start_label:
            satisfied = self.guard.is_satisfied(valuation, action.value)
            return satisfied
        return False

    def update(self, valuation, action):
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

class Fresh(SymbolicValue):
    def __init__(self, index):
        super().__init__(index)

    def __str__(self):
        return "f" + str(self.index)

    def __repr__(self):
        return self.__str__()

class Register(SymbolicValue):
    def __init__(self, index):
        super().__init__(index)

    def __str__(self):
        return "r" + str(self.index)

    def __repr__(self):
        return self.__str__()



class IORATransition(RATransition):
    def __init__(self, start_state, start_label, guard, assignment, output_label, output_mapping, output_assignment, end_state):
        super().__init__(start_state, start_label, guard, assignment, end_state)
        self.guard = guard
        self.assignment = assignment
        self.output_label = output_label
        self.output_mapping = output_mapping
        self.output_assignment =output_assignment

    def output(self, valuation, values):
        if type(self.output_mapping) == Fresh:
            return Action(self.output_label, max(values) + 1)
        else:
            return Action(self.output_label, valuation[self.output_mapping])

    def output_update(self, valuation, action):
        return self.output_assignment.update(valuation, action.value)

    def __str__(self, shortened=False):
        trans_str = "{0}({1}) {2} / {3}({4}) {5}  {6}"\
            .format(self.start_label, self.guard, self.assignment, self.output_label,\
                    self.output_mapping, self.output_assignment, self.end_state)

        if not shortened:
            trans_str = self.start_label + "  " + trans_str
        return trans_str

# some methods shared between the different register automatas
class RegisterMachine():
    def _fired_transition(self, transitions, reg_val, action):
        """Retrieves the transition fired based on the action and valuation"""
        fired_transitions = [trans for trans in transitions if trans.is_enabled(reg_val, action)]

        # the number of fired transitions can be more than one since we could have multiple equalities
        # todo (merge into or guard?)
        if len(fired_transitions) == 0:
            raise NoTransitionFired

        if len(fired_transitions) > 1:
            raise MultipleTransitionsFired
        return fired_transitions[0]

class RegisterAutomaton(Acceptor, RegisterMachine):
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
        tr_str = "({0}:{1})".format(crt_state, reg_val)
        for action in trace:
            transitions = self.transitions(crt_state, action.label)
            fired_transition = super()._fired_transition(transitions, reg_val, action)
            reg_val = fired_transition.update(reg_val, action)
            crt_state = fired_transition.end_state
            tr_str += " {0} ({1}:{2})".format(action, crt_state, reg_val)

        # print(tr_str)
        return crt_state


class IORegisterAutomaton(Transducer, RegisterMachine):
    def __init__(self, locations, loc_to_trans, registers):
      super().__init__(locations, loc_to_trans)
      self._registers = registers

    def registers(self) -> List[Register]:
        return self._registers

    def transitions(self, state: str, label:str = None) -> List[IORATransition]:
        return super().transitions(state, label)

    def state(self, trace: List[Action]) -> str:
        (reached_state, valuation, values) = self._machine_state(trace)
        return reached_state

    def _machine_state(self, trace: List[Action]) -> (str, dict, set):
        init = -1
        # maintains the set of values encountered
        values = set()
        reg_val = dict()
        for reg in self.registers():
            reg_val[reg] = init

        crt_state = self.start_state()
        for action in trace:
            values.add(action.value)
            transitions = self.transitions(crt_state, action.label)
            fired_transition = super()._fired_transition(transitions, reg_val, action)
            reg_val = fired_transition.update(reg_val, action)

            # the transition should give us the output action
            output_action = fired_transition.output(reg_val, values)
            # based on this output, the transition should update the set of registers
            reg_val = fired_transition.output_update(reg_val, output_action)

            crt_state = fired_transition.end_state
        return (crt_state, reg_val, values)

    def output(self, trace: List[Action]) -> Action:
        if len(trace) == 0:
            return None
        else:
            (reached_state, valuation, values) = self._machine_state(trace[:-1])
            action = trace[-1]
            transitions = super().transitions(reached_state, action.label)
            fired_transition = super()._fired_transition(transitions, valuation, action)
            output = fired_transition.output(valuation, values)
            return output

class MutableRegisterAutomaton(RegisterAutomaton, MutableAcceptorMixin):
    def __init__(self):
        super().__init__([], dict(), dict(), [])

    def add_transition(self, state:str, transition:RATransition):
        super().add_transition(state, transition)
        for reg in transition.guard.registers():
            if reg not in self._registers:
                self._registers.append(reg)

    def to_immutable(self) -> RegisterAutomaton:
        return RegisterAutomaton(self._states, self._state_to_acc, self._state_to_trans, self._registers)

class MutableIORegisterAutomaton(IORegisterAutomaton, MutableAutomatonMixin):
    def __init__(self):
        super().__init__([], dict(), [])

    def add_transition(self, state:str, transition:IORATransition):
        super().add_transition(state, transition)
        for reg in transition.guard.registers():
            if reg not in self._registers:
                self._registers.append(reg)

    def to_immutable(self):
        return IORegisterAutomaton(self._states, self._state_to_trans, self._registers)


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
        self._register = register

    def update(self, valuation, value):
        new_valuation = dict(valuation)
        new_valuation[self._register] = value
        return new_valuation

    def __str__(self):
        return "{0}:=p".format(str(self._register))


class NoAssignment(Assignment):
    def __init__(self):
        super().__init__()

    def update(self, valuation, value):
        return dict(valuation)

    def __str__(self):
        return "r:=r"

