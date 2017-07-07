from abc import ABCMeta, abstractmethod
from typing import List

"""The most basic transition class available"""


class Transition():
    def __init__(self, start_state, start_label, end_state):
        self.start_state = start_state
        self.start_label = start_label
        self.end_state = end_state

    def __str__(self, shortened=False):
        short = "{0} -> {1}".format(self.start_label, self.end_state)
        if not shortened:
            return "{0} {1}".format(self.start_state, short)
        else:
            return short


"""Exception raised when no transition can be fired"""


class NoTransitionFired(Exception):
    pass


"""Exception raised when several transitions can be fired in a deterministic machine"""


class MultipleTransitionsFired(Exception):
    pass


"""A basic abstract automaton model"""


class Automaton(metaclass=ABCMeta):
    def __init__(self, states, state_to_trans):
        super().__init__()
        self._states = states
        self._state_to_trans = state_to_trans
        self._acc_seq = {}

    def start_state(self):
        return self._states[0]

    def acc_seq(self, state):
        return self._acc_seq[state]

    def states(self):
        return list(self._states)

    def transitions(self, state, label=None) -> List[Transition]:
        if label is None:
            return list(self._state_to_trans[state])
        else:
            return list([trans for trans in self._state_to_trans[state] if trans.start_label == label])

    def state(self, trace):
        """state function which also provides a basic implementation"""
        crt_state = self.start_state()
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

        return crt_state

    def input_labels(self):
        return set([trans.start_label for trans in self.transitions(self.start_state())])

    @abstractmethod
    def output(self, trace):
        pass

    # Basic __str__ function which works for most FSMs.
    def __str__(self):
        str_rep = ""
        for state in self.states():
            str_rep += str(state) + "\n"
            for tran in self.transitions(state):
                str_rep += "\t" + tran.__str__(shortened=True) + "\n"

        return str_rep

class MutableAutomatonMixin(metaclass=ABCMeta):
    def add_state(self, state):
        if state not in self._states:
            self._states.append(state)

    def add_transition(self, state, transition):
        if state not in self._state_to_trans:
            self._state_to_trans[state] = []
        self._state_to_trans[state].append(transition)

    def add_acc_seq(self, state, trace):
        self._acc_seq[state] = trace

    @abstractmethod
    def to_immutable(self) -> Automaton:
        pass


"""An automaton model that generates output"""


class Transducer(Automaton, metaclass=ABCMeta):
    def __init__(self, states, state_to_trans):
        super().__init__(states, state_to_trans)

    @abstractmethod
    def output(self, trace):
        pass

    def output_labels(self):
        return set([trans.output for state in self.states() for trans in self.transitions(state)])



"""An automaton model whose states are accepting/rejecting"""


class Acceptor(Automaton, metaclass=ABCMeta):
    def __init__(self, states, state_to_trans, state_to_acc):
        super().__init__(states, state_to_trans)
        self._state_to_acc = state_to_acc

    def is_accepting(self, state):
        return self._state_to_acc[state]

    def accepts(self, trace):
        state = self.state(trace)
        is_acc = self.is_accepting(state)
        return is_acc

    def output(self, trace):
        self.accepts(trace)

    def __str__(self):
        return str(self._state_to_acc) + "\n" + super().__str__()


class MutableAcceptorMixin(MutableAutomatonMixin, metaclass=ABCMeta):
    def add_state(self, state, accepts):
        super().add_state(state)
        self._state_to_acc[state] = accepts


def get_acc_seq(aut : Automaton, runner, old_acc_seq = dict()):
    new_acc_seq = {aut.state(acc_seq):acc_seq for acc_seq in old_acc_seq.values()}
    not_covered = [state for state in aut.states() if state not in new_acc_seq.keys()]
    ptree = get_prefix_tree(aut)
    for state in not_covered:
        trace = runner(ptree.path(state))
        new_acc_seq[state] = trace
    return new_acc_seq


def get_prefix_tree(aut : Automaton):
    visited  = set()
    to_visit = set()
    root = PrefixTree(aut.start_state())
    to_visit.add(root)
    while len(to_visit) > 0:
        crt_node = to_visit.pop()
        visited.add(crt_node.state)
        transitions = aut.transitions(crt_node.state)
        for trans in transitions:
            if trans.end_state not in visited:
                child_node = PrefixTree(trans.end_state)
                crt_node.add_child(trans, child_node)
    return root




class PrefixTree():
    def __init__(self, state):
        self.state = state
        self.tr_tree:dict = {}
        self.parent = None

    def add_child(self, trans, tree):
        self.tr_tree[trans] = tree
        self.tr_tree[trans].parent = self

    def path(self, state) -> List[Transition]:
        if len(self.tr_tree):
            return None
        else:
            for (tran, child) in self.tr_tree.items():
                path = child.path(state)
                if path is not None:
                    return [tran] + path
            return None