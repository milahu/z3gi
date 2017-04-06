from z3gi.encoders import interface
import z3

class NonDeterminismError(Exception):
    """A NonDeterminismError is raised when there are conflicting labels for a string."""
    pass

class Encoder(interface.Encoder):
    """An Encoder constructs a set of constraints for labeled strings.
    This implementation uses the 'expressive' encoding for DFA models.
    """
    SYMBOL = z3.DeclareSort('SYMBOL')
    NODE = z3.DeclareSort('NODE')
    STATE = z3.IntSort()
    LABEL = z3.BoolSort()

    def __init__(self, quantifiers=True, inequalities=False):
        """Returns a new expressive Encoder.

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
        self.repr = z3.Function('repr', self.NODE, self.STATE)
        self.n = z3.Int('n')

        # Alphabet
        self.alphabet = {}

        # Data structure
        self.nodes = []
        self.counter = 0
        self.apt = _node(self)

    def __setitem__(self, string, label):
        """Adds constraints for a string, label pair.
        Raises a NonDeterminsmError if string is already encoded with another label.
        """
        try:
            self.apt[string] = label
        except NonDeterminismError:
            raise NonDeterminismError("string: %s, label: %s, already encoded other label" % (string, label))

    def encode(self, n):
        """Returns a list of constraints for a DFA with n states."""
        axioms = [self.n == n]
        states = [z3.Const('state%d' % i, self.STATE) for i in range(0, n)]
        axioms += [states[i] == i for i in range(0, n)]

        # free variables used in z3's forall must be declared
        node = z3.Const('node', self.NODE)

        quantifiers = self.settings['quantifiers']
        inequalities = self.settings['inequalities']
        if quantifiers and inequalities:
            axioms.append(z3.ForAll(node, z3.And(self.repr(node) >= 0, self.repr(node) < self.n), patterns = [self.repr(node)]))
        elif quantifiers and not inequalities:
            axioms.append(z3.ForAll(node, z3.Or([self.repr(node) == state for state in states]), patterns = [self.repr(node)]))
        elif not quantifiers and inequalities:
            for node in self.nodes:
                axioms.append(z3.And(self.repr(node) >= 0, self.repr(node) < self.n))
        else: # not quantifiers and not inequalities
            for node in self.nodes:
                axioms.append(z3.Or([self.repr(node) == state for state in states]))

        return axioms + self.constraints

    def __len__(self):
        """Returns the number of encoded labels."""
        self.apt.count_labels()

    def _add_trans_constraint(self, node, symbol, child):
        """Adds a transition constraint for the representatives of node and child."""
        if symbol not in self.alphabet:
            self.alphabet[symbol] = z3.Const(symbol, self.SYMBOL)
        self.constraints.append(self.trans(self.repr(node), self.alphabet[symbol]) == self.repr(child))

    def _add_out_constraint(self, node, label):
        """Adds an output constraint for the representative of node."""
        self.constraints.append(self.out(self.repr(node)) == label)

class _node(object):
    """A helper class for implementing an augmented prefix tree (APT)."""

    def __init__(self, encoder):
        """Returns an APT node.

        Keyword arguments:
        encoder -- the encoder for this node
        """
        self.encoder = encoder
        self.children = {}
        self.label = None
        self.name = z3.Const('node%d' % self.encoder.counter, encoder.NODE)
        self.encoder.counter += 1
        self.encoder.nodes.append(self.name)

    def __setitem__(self, string, label):
        """Recursively adds the string, label pair to the APT."""
        if len(string) == 0:
            if self.label is not None and self.label != label:
                raise NonDeterminismError()
            else:
                self.label = bool(int(label))
                self.encoder._add_out_constraint(self.name, self.label)
                return

        symbol, string = string[0], string[1:]
        try:
            self.children[symbol][string] = label
        except KeyError:
            child = _node(self.encoder)
            self.children[symbol] = child
            self.encoder._add_trans_constraint(self.name, symbol, child.name)
            self.children[symbol][string] = label

    def __len__(self):
        """Returns the number of nodes in the APT
        (this is not necessarily the number of string, label pairs).
        """
        n = 1
        for symbol in self.children.keys():
            n = n + len(self.children[symbol])
        return n

    def count_labels(self):
        """Returns the number of labels in the APT."""
        n = 1 if self.label != None else 0
        for symbol in self.children.keys():
            n = n + self.children[symbol].count_labels()
        return n
