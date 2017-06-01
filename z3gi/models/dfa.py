#TODO allow customization for the else branch of z3 functions
#TODO let encoders construct and return these types of models
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
        self.alphabet = alphabet
        self.states = states
        self.start = start
        self.trans = trans
        self.out = out

        self.model = None

    def __getitem__(self, string):
        """Returns the computation of the provided string on the model.
        Raises a NotAssignedError if the model is not assigned yet.
        Raises a KeyError if string contains an unknown symbol.

        Keyword arguments:
        string -- an iterable of symbol identifiers
        """
        if not self.assigned():
            raise NotAssignedError()

        state = self.start
        for s in string:
            symbol = self.alphabet[s]
            state = self.model.evaluate(self.trans(state, symbol))
        return z3.is_true(self.model.evaluate(self.out(state)))

    def export(self, f):
        """Writes the model in DOT format to text stream f.
        Raises a NotAssignedError if the model is not assigned yet.
        """
        if not self.assigned():
            raise NotAssignedError()
        # TODO

    def assign(self, model):
        """Assigns the model.
        Returns a ModelError if not all the constants, terms and functions of this model's definition can be evaluated on the model's assignment.

        Keyword arguments:
        model -- a z3.ModelRef assignment for the constants, terms and functions in this model
        """
        for symbol in self.alphabet:
            if interface.is_uninterpreted(model.evaluate(self.alphabet[symbol])):
                raise ModelError("Symbol %s is uninterpreted in model %s." % (symbol, model))
        for i, state in enumerate(self.states):
            if interface.is_uninterpreted(model.evaluate(state)):
                raise ModelError("State %d is uninterpreted in model %s." % (i, model))
        self.model = model
