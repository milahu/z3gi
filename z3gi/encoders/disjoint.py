from z3gi.encoders import interface
from z3gi.models import dfa
import z3

class LabelError(Exception):
    """A LabelError is raised when an unknown label is provided."""
    pass

class NonDeterminismError(Exception):
    """A NonDeterminismError is raised when there are conflicting labels for a string."""
    pass

class SymbolError(Exception):
    """A SymbolError is raised when getting a string contains a symbol that is not in the alphabet."""
    pass

class EncodeError(Exception):
    """An EncodeError is raised when trying to encode with not enough states."""
    pass

class Encoder(interface.Encoder):
    """An Encoder constructs a set of constraints for labeled strings.
    This implementation uses the 'natural' encoding for DFA models.
    """
    SYMBOL = z3.DeclareSort('SYMBOL')
    STATE = z3.IntSort()
    LABEL = z3.BoolSort()

    def __init__(self, k, quantifiers=True, inequalities=False):
        """Returns a new natural Encoder.

        Keyword arguments:
        quantifiers -- use z3.ForAll for quantifying over states (default True)
        inequalities -- use linear inequalities in constraints (default False)
        """
        self.constraints = []

        # Settings
        self.settings = {'quantifiers':quantifiers, 'inequalities':inequalities}

        # Z3 functions and constants
        self.trans = z3.Function('trans', self.STATE, self.SYMBOL, self.STATE)
        self.out = z3.Function('out', self.STATE, self.LABEL)
        self.start = [z3.Const('start%d' % i, self.STATE) for i in range(k)]
        self.n = z3.Int('n')
        self.k = k

        # Alphabet
        self.alphabet = {}

        # Data structure
        self.sample = {}

    ACCEPT = 1
    REJECT = 0
    UNKOWN = -1
    def __setitem__(self, string, label):
        """Adds constraints for a string, label pair."""
        if label != ACCEPT and label != REJECT and label != UNKNOWN:
            raise LabelError("Unknown label %s" % label)

        string = ' '.join(string)
        if string in self.sample and self.sample[string] != label:
            raise NonDeterminismError("string: %s, label: %s, already encoded other label" % (string, label))
        self.sample[string] = True

        def transitions(s, i):
            """Returns nested transitions for symbols in string s."""
            if len(s) == 0:
                return self.start[i]
            if s[-1] not in self.alphabet:
                self.alphabet[s[-1]] = z3.Const(s[-1], self.SYMBOL)
            return self.trans(transitions(s[:-1], i), self.alphabet[s[-1]])

        if label == UNKNOWN:
            constraint = z3.Or([z3.And([self.out(transitions(string.split(), i)) == True] + [self.out(transitions(string.split(), j)) == False for j in range(self.k) if j != i]) for i in range(self.k)])
        else if label == ACCEPT:
            constraint = z3.And([self.out(transitions(string.split(), i)) == True for i in range(self.k)])
        else if label == REJECT:
            constraint = z3.And([self.out(transitions(string.split(), i)) == False for i in range(self.k)])

        self.constraints.append(constraint)

#    def __getitem__(self, string):
#        """Returns the Z3 expression that one can evaluate on a natural model to obtain the label for string."""
#
#        def transitions(s):
#            """Returns nested transitions for symbols in string s."""
#            if len(s) == 0:
#                return self.start
#            if s[-1] not in self.alphabet:
#                raise SymbolError("Symbol %s not in alphabet" % s[-1])
#            return self.trans(transitions(s[:-1]), self.alphabet[s[-1]])
#
#        return self.out(transitions(string))

    def encode(self, n):
        """Returns a list of constraints for a DFA with n states."""
        if n < self.k:
            raise EncodeError("Not enough states %d" % n)

        states = self.start + [z3.Const('state%d' % i, self.STATE) for i in range(n-self.k)]
        model = dfa.DFA(self.alphabet, states, self.start, self.trans, self.out)

        axioms = [self.n == n]
        axioms += [states[i] == i for i in range(0, n)]

        # free variables used in z3's forall must be declared
        state = z3.Const('state', self.STATE)
        symbol = z3.Const('symbol', self.SYMBOL)

        quantifiers = self.settings['quantifiers']
        inequalities = self.settings['inequalities']
        if quantifiers and inequalities:
            axioms.append(z3.ForAll([state, symbol], z3.And(self.trans(state, symbol) >= 0, self.trans(state, symbol) < self.n), patterns = [self.trans(state, symbol)]))
        elif quantifiers and not inequalities:
            axioms.append(z3.ForAll([state, symbol], z3.Or([self.trans(state, symbol) == s for s in states]), patterns = [self.trans(state, symbol)]))
        elif not quantifiers and inequalities:
            for symbol in self.alphabet:
                for state in states:
                    axioms.append(z3.And(self.trans(state, self.alphabet[symbol]) >= 0, self.trans(state, self.alphabet[symbol]) < self.n))
        else: # not quantifiers and not inequalities
            for symbol in self.alphabet:
                for state in states:
                    axioms.append(z3.Or([self.trans(state, self.alphabet[symbol]) == target for target in states]))

        return axioms + self.constraints, model

    def __len__(self):
        """Returns the number encoded strings."""
        return len(self.sample)
