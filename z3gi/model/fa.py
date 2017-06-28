from z3gi.model import Transition, Acceptor, Transducer, NoTransitionFired, MultipleTransitionsFired, Automaton
from abc import ABCMeta, abstractmethod
import itertools
import collections
from typing import List

Symbol = str
State = str
Label = str
Output = str

class DFA(Acceptor):
    def __init__(self, states, state_to_trans, state_to_acc):
      super().__init__(states, state_to_trans, state_to_acc)

    def transitions(self, state: State, label:Label = None) -> List[Transition]:
        return super().transitions(state, label)

    def state(self, trace: List[Symbol]) -> State:
        crt_state = super().state(trace)
        # print(tr_str)
        return crt_state

class MooreMachine(Transducer):
    def __init__(self, states, state_to_trans, state_to_out):
        super().__init__(states, state_to_trans)
        self.state_to_out = state_to_out

    def transitions(self, state: State, label:Label = None) -> List[Transition]:
        return super().transitions(state, label)

    def state(self, trace: List[Symbol]) -> State:
        crt_state = super().state(trace)
        return crt_state

    def output(self, trace: List[Symbol]) -> Output:
        crt_state = self.state(trace)
        return self.state_to_out[crt_state]

class MealyMachine(Transducer):
    def __init__(self, states, state_to_trans, state_to_out):
        super().__init__(states, state_to_trans)
        self.state_to_out = state_to_out

    def transitions(self, state: State, label: Label = None) -> List[IOTransition]:
        return super().transitions(state, label)

    def state(self, trace: List[Symbol]) -> State:
        crt_state = super().state(trace)
        return crt_state

    def output(self, trace: List[Symbol]) -> Output:
        if len(trace) == 0:
            return  None
        else:
            state_before = self.state(trace[:-1])
            trans = self.transitions(state_before, trace[-1])
            return trans.output

class IOTransition(Transition):
    def __init__(self, start_state, start_label, output, end_state):
        super().__init__(start_state, start_label, end_state)
        self.output = output



