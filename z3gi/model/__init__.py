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



def defined_formalisms():
    """retrieves a dictionary containing the formalisms implemented and their respective classes"""
    import inspect
    sc = dict()
    crt = Automaton
    to_visit = set(crt.__subclasses__())
    while len(to_visit) > 0:
        subclass = to_visit.pop()
        if not inspect.isabstract(subclass) and not subclass.__name__.startswith("Mutable"):
            sc[subclass.__name__] = subclass
        else:
            to_visit = to_visit.union(to_visit, set(subclass.__subclasses__()))
    return sc


"""A basic abstract automaton model"""


class Automaton(metaclass=ABCMeta):
    def __init__(self, states, state_to_trans, acc_trans_seq={}):
        super().__init__()
        self._states = states
        self._state_to_trans = state_to_trans
        self._acc_trans_seq = acc_trans_seq

    def start_state(self):
        return self._states[0]

    def acc_trans_seq(self, state=None) -> List[Transition]:
        """returns the access sequence to a state in the form of transitions"""
        if state is not None:
            return list(self._acc_trans_seq[state])
        else:
            return dict(self._acc_trans_seq)

    def acc_seq(self, state=None):
        """returns the access sequence to a state in the form of sequences of inputs"""
        if state is not None:
            if len(self._acc_trans_seq) == 0:
                raise Exception("Access sequences haven't been defined for this machine")
            return self._seq(self._acc_trans_seq[state])
        else:
            return {state:self._seq(self._acc_trans_seq[state]) for state in self.states()}

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

    @abstractmethod
    def _seq(self, transitions:List[Transition])->List[object]:
        """returns the sequence of inputs generated by execution of these transitions"""
        pass

    def input_labels(self):
        return set([trans.start_label for trans in self.transitions(self.start_state())])

    @abstractmethod
    def output(self, trace):
        pass

    # Basic __str__ function which works for most FSMs.
    def __str__(self):
        str_rep = ""
        for (st, acc_seq) in self._acc_trans_seq.items():
            str_rep += "acc_seq("+ str(st) +") = " + str(list(map(str,acc_seq))) + "\n"
        for state in self.states():
            str_rep += str(state) + "\n"
            for tran in self.transitions(state):
                str_rep += "\t" + tran.__str__(shortened=True) + "\n"

        return str_rep

class MutableAutomatonMixin(metaclass=ABCMeta):
    def add_state(self:Automaton, state):
        if state not in self._states:
            self._states.append(state)

    def add_transition(self:Automaton, state, transition):
        if state not in self._state_to_trans:
            self._state_to_trans[state] = []
        self._state_to_trans[state].append(transition)

    def generate_acc_seq(self:Automaton):
        """generates access sequences for an automaton. It optionally takes in old access sequences, which are """
        new_acc_seq = dict()
        ptree = get_prefix_tree(self)
        for state in self.states():
            pred = lambda x: (x.state == state)
            node = ptree.find_node(pred)
            if node is None:
                raise Exception("Could not find state {0} in tree {1} \n for model \n {2}".format(state, ptree, self))
            new_acc_seq[state] = node.path()
        assert(len(new_acc_seq) == len(self.states()))
        self._acc_trans_seq = new_acc_seq

    @abstractmethod
    def to_immutable(self) -> Automaton:
        pass


"""An automaton model that generates output"""


class Transducer(Automaton, metaclass=ABCMeta):
    def __init__(self, states, state_to_trans, acc_trans_seq={}):
        super().__init__(states, state_to_trans, acc_trans_seq)

    @abstractmethod
    def output(self, trace):
        pass



"""An automaton model whose states are accepting/rejecting"""


class Acceptor(Automaton, metaclass=ABCMeta):
    def __init__(self, states, state_to_trans, state_to_acc, acc_trans_seq={}):
        super().__init__(states, state_to_trans, acc_trans_seq)
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
                to_visit.add(child_node)
    return root


class PrefixTree():
    def __init__(self, state):
        self.state = state
        self.tr_tree:dict = {}
        self.parent:PrefixTree = None

    def add_child(self, trans, tree):
        self.tr_tree[trans] = tree
        self.tr_tree[trans].parent = self

    def path(self) -> List[Transition]:
        if self.parent is None:
            return []
        else:
            for (tr, node) in self.parent.tr_tree.items():
                if node is self:
                    return self.parent.path()+[tr]
            raise Exception("Miscontructed tree")

    def find_node(self, predicate):
        if predicate(self):
            return self
        elif len(self.tr_tree) == 0:
            return None
        else:
            for (tran, child) in self.tr_tree.items():
                node = child.find_node(predicate)
                if node is not None:
                    return node
            return None

    def __str__(self, tabs=0):
        space = "".join(["\t" for _ in range(0, tabs)])
        tree = "(n_{0}".format(self.state)
        for (tr, node) in self.tr_tree.items():
            tree += "\n" + space + " {0} -> {1}".format(tr, node.__str__(tabs=tabs + 1))
        tree += ")"
        return tree