#TODO allow customization for the else branch of z3 functions
import sys
import z3
from z3gi.models import interface

class NotAssignedError(Exception):
    """A NotAssignedError is raised when the variables of a model have not been assigned a value yet."""
    pass

class ModelError(Exception):
    """A ModelError is returned if not all the constants, terms and functions of a model's definition can be evaluated on a model's assignment.
    """

class DFA(interface.Model):
    """A deterministic finite automaton (DFA) is a model that accepts and rejects strings."""
    def __init__(self, alphabet, states, start, trans, out):
        """Returns a new DFA.

        Keyword arguments:
        alphabet -- a mapping of symbols to z3 constants or terms
        states -- a list of z3 constants or terms for states
        start -- a z3 constant or term for the start state
        trans -- a z3 function from states and symbols to states
        out -- a z3 function from states to z3 boolean expressions
        """
        self.model = None
        self._statemap = None
        self._alphabetmap = None

        self.alphabet = alphabet
        self.states = {"state%d" % i:state for i, state in enumerate(states)}
        self._start = start
        self.trans = trans
        self.out = out

    def __getitem__(self, string):
        """Returns the computation of the provided string on the model.
        Raises a NotAssignedError if the model is not assigned yet.
        Raises a KeyError if string contains an unknown symbol.

        Keyword arguments:
        string -- an iterable of symbol identifiers
        """
        if not self.assigned():
            raise NotAssignedError()

        state = self._start
        for s in string:
            symbol = self.alphabet[s]
            state = self.model.evaluate(self.trans(state, symbol))
        return z3.is_true(self.model.evaluate(self.out(state)))

    def export(self, fn=None):
        """Prints the model in DOT format
        Raises a NotAssignedError if the model is not assigned yet.

        If no filename is provided, it prints to sys.stdout

        Keyword arguments:
        fn -- the file to print to (default None)
        """
        if not self.assigned():
            raise NotAssignedError()
        f = open(fn, 'w') if fn is not None else sys.stdout
        print('digraph g {', file=f)
        print('__start [label="" shape="none"];', file=f)

        for state in self.states:
            label = "doublecircle" if self.is_accepting(state) else "circle"
            print('%s shape="%s" label="%s"];\n' % (state, label, state), file=f)

        for state in self.states:
            for symbol in self.alphabet:
                target = self.transition(state, symbol)
                print('%s -> %s [label="%s"];' % (state, target, symbol), file=f)

        print('__start -> %s;' % self.start(), file=f)
        print('}', file=f)

        if fn is not None:
            f.close()

    def assign(self, model):
        """Assigns the model.
        Returns a ModelError if not all the constants, terms and functions of this model's definition can be evaluated on the model's assignment.

        Keyword arguments:
        model -- a z3.ModelRef assignment for the constants, terms and functions in this model
        """
        self._statemap = {model.evaluate(value):key for key, value in self.states.items()}
        self._alphabetmap = {model.evaluate(value):key for key, value in self.alphabet.items()}
        self.model = model

    def is_accepting(self, state):
        """Returns True if state is accepting and False otherwise.

        Raises a NotAssignedError if the model has not yet been assigned.

        Keyword arguments:
        state -- a state name that is in self.states
        """
        if not self.assigned():
            raise NotAssignedError()

        return z3.is_true(self.model.evaluate(self.out(self.states[state])))

    def state(self, string):
        """Returns the name of the state reached after computing the given string on the model.

        Raises a NotAssignedError if the model has not yet been assigned.

        Keyword arguments:
        string -- an iterable of symbol names in self.alphabet
        """
        if not self.assigned():
            raise NotAssignedError()

        state = self.model.evaluate(self._start)
        for symbol in string:
            state = self.model.evaluate(self.trans(state, self.alphabet[symbol]))
        return self._statemap[state]

    def start(self):
        """Returns the name of the start state.

        Raises a NotAssignedError if the model has not yet been assigned.

        Keyword arguments:
        string -- an iterable of symbol names in self.alphabet
        """
        if not self.assigned():
            raise NotAssignedError()

        return self.state('')

    def transition(self, state, symbol):
        """Returns the state reached by transitioning from state with symbol.

        Raises a NotAssignedError if the model has not yet been assigned.

        Keyword arguments:
        state -- a state name that is in self.states
        symbol -- a symbol name that is in self.alphabet
        """
        if not self.assigned():
            raise NotAssignedError()

        z3state = self.states[state]
        z3symbol = self.alphabet[symbol]
        z3target = self.model.evaluate(self.trans(z3state, z3symbol))
        return self._statemap[z3target]
