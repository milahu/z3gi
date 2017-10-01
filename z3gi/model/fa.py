from typing import List

from model import MutableAutomatonMixin, MutableAcceptorMixin, Transition, Acceptor, Transducer


Symbol = str
State = str
Label = str
Output = str


class IOTransition(Transition):
    def __init__(self, start_state, start_label, output, end_state):
        super().__init__(start_state, start_label, end_state)
        self.output = output

    def __str__(self, shortened=False):
        short = "{0}/{1} -> {2}".format(self.start_label, self.output, self.end_state)
        if not shortened:
            return "{0} {1}".format(self.start_state, short)
        else:
            return short

class DFA(Acceptor):
    def __init__(self, states, state_to_trans, state_to_acc, acc_trans_seq={}):
        super().__init__(states, state_to_trans, state_to_acc, acc_trans_seq)

    def transitions(self, state: State, label:Label = None) -> List[Transition]:
        return super().transitions(state, label)

    def state(self, trace: List[Symbol]) -> State:
        crt_state = super().state(trace)
        return crt_state

    def _seq(self, transitions: List[Transition]):
        return [trans.start_label for trans in transitions]

class MutableDFA(DFA, MutableAcceptorMixin):
    def __init__(self):
        super().__init__([], {}, {})

    def _runner(self):
        return None

    def to_immutable(self) -> DFA:
        return DFA(self._states, self._state_to_trans, self._state_to_acc, self.acc_trans_seq())

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

    def _seq(self, transitions:List[Transition]):
        #trace = [(trans.start_label, self.state_to_out[trans.end_state]) for trans in transitions]
        return [trans.start_label for trans in transitions]#trace

class MealyMachine(Transducer):
    def __init__(self, states, state_to_trans, acc_trans_seq={}):
        super().__init__(states, state_to_trans, acc_trans_seq)

    def transitions(self, state: State, label: Label = None) -> List[IOTransition]:
        return super().transitions(state, label)

    def state(self, trace: List[Symbol]) -> State:
        crt_state = super().state(trace)
        return crt_state

    def _seq(self, transitions:List[IOTransition]):
        #trace = [(trans.start_label, trans.output) for trans in transitions]
        return [trans.start_label for trans in transitions]

    def output(self, trace: List[Symbol]) -> Output:
        if len(trace) == 0:
            return  None
        else:
            state_before = self.state(trace[:-1])
            trans = self.transitions(state_before, trace[-1])
            assert(len(trans) == 1)
            return trans[0].output

class MutableMealyMachine(MealyMachine, MutableAutomatonMixin):
    def __init__(self):
        super().__init__([], {})

    def to_immutable(self) -> MealyMachine:
        return MealyMachine(self._states, self._state_to_trans, self.acc_trans_seq())
