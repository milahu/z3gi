from z3gi.encoders import interface
import z3

class NonDeterminismError(Exception):
    """A NonDeterminismError is raised when there are conflicting labels for a string."""
    pass

class Encoder(interface.Encoder):
    """An Encoder constructs a set of constraints for labeled strings.
    This implementation uses the 'natural' encoding for DFA models.
    """
    SYMBOL = z3.DeclareSort('SYMBOL')
    STATE = z3.IntSort()
    LABEL = z3.BoolSort()

    def __init__(self, quantifiers=True, inequalities=False):
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
        self.start = z3.Const('state0', self.STATE)
        self.n = z3.Int('n')

        # Alphabet
        self.alphabet = {}

        # Data structure
        self.sample = {}

    def __setitem__(self, string, label):
        """Adds constraints for a string, label pair.
        Raises a NonDeterminsmError if string is already encoded with another label.
        """
        string = ' '.join(string)
        label = bool(int(label))
        if string in self.sample and self.sample[string] != label:
            raise NonDeterminismError("string: %s, label: %s, already encoded other label" % (string, label))
        self.sample[string] = label

        def transitions(s):
            """Returns nested transitions for symbols in string s."""
            if len(s) == 0:
                return self.start
            if s[-1] not in self.alphabet:
                self.alphabet[s[-1]] = z3.Const(s[-1], self.SYMBOL)
            return self.trans(transitions(s[:-1]), self.alphabet[s[-1]])

        self.constraints.append(self.out(transitions(string.split())) == label)

    def encode(self, n):
        """Returns a list of constraints for a DFA with n states."""
        axioms = [self.n == n]
        states = [self.start] + [z3.Const('state%d' % i, self.STATE) for i in range(1, n)]
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

        return axioms + self.constraints

    def __len__(self):
        """Returns the number encoded labels."""
        return len(self.sample)
