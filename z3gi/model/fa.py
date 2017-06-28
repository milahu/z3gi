from z3gi.model import Transition, Acceptor, NoTransitionFired, MultipleTransitionsFired
from abc import ABCMeta, abstractmethod
import itertools
import collections
from typing import List

Symbol = str
State = str
Label = str

class DFA(Acceptor):
    def __init__(self, locations, loc_to_acc, loc_to_trans, registers):
      super().__init__(locations, loc_to_trans, loc_to_acc)
      self._registers = registers

    def transitions(self, state: State, label:Label = None) -> List[Transition]:
        return super().transitions(state, label)

    def state(self, trace: List[Symbol]) -> State:

        crt_state = self.start_state()
        tr_str = crt_state
        for symbol in trace:
            transitions = self.transitions(crt_state, symbol)
            fired_transitions = [trans for trans in transitions if trans.start_label == symbol]

            # the number of fired transitions can be more than one since we could have multiple equalities
            if len(fired_transitions) == 0:
                raise NoTransitionFired

            if len(fired_transitions) > 1:
                raise MultipleTransitionsFired

            fired_transition = fired_transitions[0]
            crt_state = fired_transition.end_state
            tr_str += " {0} {1}".format(symbol, crt_state)

        # print(tr_str)
        return crt_state


