from z3gi.encoders import interface
from z3gi.models import dfa
import z3

class NonDeterminismError(Exception):
    """A NonDeterminismError is raised when there are conflicting labels for a string."""
    pass

class Encoder(interface.Encoder):
    """An Encoder constructs a set of constraints for labeled strings.
    This implementation uses the encoding from Heule and Verwer for DFA models.
    For a description of this encoding see 'Software model synthesis using satisfiability solvers', Table 1.
    """

    def __init__(self, redundant=False):
        """Returns a new propositional Encoder.

        Keyword arguments:
        redundant -- use redundant constraints (default False)
        """
        # Settings
        self.settings = {'redundant':redundant}

        # Variables
        # (defined over vertexes (v,w), states (i,j) and symbols (a))
        self.x = [] # x[v][i] = True iff vertex v is represented by state i
        self.y = [] # y[a][i][j] = True iff parents of vertexes represented by state j and incoming label a are represented by state i
        self.z = [] # z[i] = True iff state i is an accepting state

        # Alphabet
        self.alphabet = {}

        # Data structure
        self.counter = 0
        self.apt = _node(self)
        self.relations = []
        self.accepting = {}
        self.rejecting = {}

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
        # TODO: construct a proper model for this implementation
        model = dfa.DFA(None, None, None, None, None)


        # Initiate variables
        for v in range(len(self.x)):
            self.x[v] = [z3.Bool('x_%d_%d' % (v, i)) for i in range(n)]
        for a in range(len(self.y)):
            self.y[a] = [[z3.Bool('y_%d_%d_%d' % (a, i, j)) for j in range(n)] for i in range(n)]
        self.z = [z3.Bool('z_%d' % i) for i in range(n)]

        # Constraints
        constraints = []
        # At least one color
        for v in range(len(self.x)):
            constraints.append(z3.Or([var for var in self.x[v]]))
        # Accepting states can not have the same color as rejecting states
        for v in self.accepting:
            for i in range(n):
                constraints.append(z3.Or(z3.Not(self.x[v][i]), self.z[i]))
        for w in self.rejecting:
            for i in range(n):
                constraints.append(z3.Or(z3.Not(self.x[w][i]), z3.Not(self.z[i])))
        # A parent relation is set when a state and its parent are colored
        for p, a, v in self.relations:
            for i in range(n):
                for j in range(n):
                    constraints.append(z3.Or(self.y[a][i][j], z3.Not(self.x[p][i]), z3.Not(self.x[v][j])))
        # Each parent relation can target at most one color
        for a in range(len(self.y)):
            for i in range(n):
                for j in range(n):
                    for h in range(n):
                        if h < j:
                            constraints.append(z3.Or(z3.Not(self.y[a][i][h]), z3.Not(self.y[a][i][j])))

        redundant = self.settings['redundant']
        if redundant:
            # Every state has at most one color
            for v in range(len(self.x)):
                for i in range(n):
                    for j in range(n):
                        if i < j:
                            constraints.append(z3.Or(z3.Not(self.x[v][i]), z3.Not(self.x[v][j])))
            # Each parent relation must target at least one color
            for a in range(len(self.y)):
                for i in range(n):
                    constraints.append(z3.Or([var for var in self.y[a][i]]))
            # A parent relation forces a state once the parent is colored
            for p, a, v in self.relations:
                for i in range(n):
                    for j in range(n):
                        constraints.append(z3.Or(z3.Not(self.y[a][i][j]), z3.Not(self.x[p][i]), self.x[v][j]))
            # All determinization conflicts explicitly added as clauses
            for v, _, w in self.relations:
                for i in range(n):
                    constraints.append(z3.Or(z3.Not(self.x[v][i]), z3.Not(self.x[w][i])))

        return constraints, model

    def __len__(self):
        """Returns the number of encoded labels."""
        self.apt.count_labels()

    def _add_trans_constraint(self, node, symbol, child):
        """Adds a transition constraint for the representatives of node and child."""
        if symbol not in self.alphabet:
            i = len(self.alphabet)
            self.alphabet[symbol] = i
            self.y.append(None)
        self.relations.append((node, self.alphabet[symbol], child))

    def _add_out_constraint(self, node, label):
        """Adds an output constraint for the representative of node."""
        if bool(int(label)):
            self.accepting[node] = True
        else:
            self.rejecting[node] = True

class _node(object):
    """A helper class for implementing an augmented prefix tree (APT)."""
    def __init__(self, solver):
        """A helper class for implementing an augmented prefix tree (APT)."""
        self.solver = solver
        self.children = {}
        self.label = None
        self.name = self.solver.counter
        self.solver.counter += 1
        self.solver.x.append(None)

    def __setitem__(self, string, label):
        """Recursively adds the string, label pair to the APT."""
        if len(string) == 0:
            if self.label is not None and self.label != bool(int(label)):
                raise NonDeterminismError()
            else:
                self.label = bool(int(label))
                self.solver._add_out_constraint(self.name, self.label)
                return

        symbol, string = string[0], string[1:]
        try:
            self.children[symbol][string] = label
        except KeyError:
            child = _node(self.solver)
            self.children[symbol] = child
            self.solver._add_trans_constraint(self.name, symbol, child.name)
            self.children[symbol][string] = label

    def __len__(self):
        """Returns the number of nodes in the APT
        (this is not necessarily the number of labels).
        """
        n = 1
        for string in self.children.strings():
            n = n + len(self.children[string])
        return n

    def count_labels(self):
        """Returns the number of labels in the APT."""
        n = 1 if self.label != None else 0
        for symbol in self.children.keys():
            n = n + self.children[symbol].count_labels()
        return n
