from z3gi.encoders import interface
import z3

class NonDeterminismError(Exception):
    """A NonDeterminismError is raised when there are conflicting output strings for an input string."""
    pass

class TraceError(Exception):
    """A TraceError is raised when input and output strings are not of the same lenght."""
    pass

class Encoder(interface.Encoder):
    """An Encoder constructs a set of constraints for input/ output traces.
    This implementation uses the 'transducer' encoding for Mealy machine models.
    """
    INPUT = z3.DeclareSort('INPUT')
    OUTPUT = z3.DeclareSort('OUTPUT')
    NODE = z3.DeclareSort('NODE')
    STATE = z3.IntSort()

    def __init__(self, quantifiers=True, inequalities=False):
        """Returns a new Mealy Encoder.

        Keyword arguments:
        quantifiers -- use z3.ForAll for quantifying over states (default True)
        inequalities -- use linear inequalities in constraints (default False)
        """
        self.constraints = []

        # Settings
        self.settings = {'quantifiers':quantifiers, 'inequalities':inequalities}

        # Z3 functions and constants
        self.trans = z3.Function('trans', self.STATE, self.INPUT, self.STATE)
        self.out = z3.Function('out', self.STATE, self.INPUT, self.OUTPUT)
        self.repr = z3.Function('repr', self.NODE, self.STATE)
        self.n

        # Alphabets
        self.inputs = {}
        self.outputs = {}

        # Data structure
        self.nodes = []
        self.counter = 0
        self.apt = _node(self)

    def __setitem__(self, inputs, outputs):
        """Adds constraint for an input/output trace.
        Raises a NonDeterminsmError if input string is already encoded with another output string.
        Raises a TraceError if input and output strings are not of the same length.
        """
        if len(inputs) != len(outputs):
            raise TraceError("Invalid trace: inputs: %s, outputs: %s" % (inputs, outputs))

        try:
            self.apt[inputs] = outputs
        except NonDeterminismError:
            raise NonDeterminismError("input: %s, output: %s, already encoded other output" % (inputs, outputs))

    def encode(self, n):
        """Returns a list of constraints for a Mealy or Moore machine with n states."""
        axioms = [self.n == n]
        states = [z3.Const('state%d' % i, self.STATE) for i in range(0, n)]
        axioms += [states[i] == i for i in range(0, n)]
        axioms += [z3.Distinct([output for output in self.outputs.values()])]

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
                axioms.append(z3.Or([self.repr(node) == states[i] for i in range(0, n)]))

        return axioms + self.constraints

    def __len__(self):
        """Returns the number of encoded outputs."""
        self.apt.count_labels()

    def _add_trans_constraint(self, node, input, child):
        """Adds a transition constraint for the representatives of node and child."""
        if input not in self.inputs:
            self.inputs[input] = z3.Const('%s' % input, self.INPUT)
        self.constraints.append(self.trans(self.repr(node), self.inputs[input]) == self.repr(child))

    def _add_out_constraint(self, node, input, output):
        """Adds an output constraint for the representative of node."""
        if output not in self.outputs:
            self.outputs[output] = z3.Const('%s' % output, self.OUTPUT)
        if input not in self.inputs:
            self.inputs[input] = z3.Const('%s' % input, self.INPUT)
        self.constraints.append(self.out(self.repr(node), self.inputs[input]) == self.outputs[output])

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

    def __setitem__(self, inputs, outputs):
        """Recursively adds the input, output trace to the APT."""
        if len(inputs) == 0:
            return
        input, inputs = inputs[0], inputs[1:]
        output, outputs = outputs[0], outputs[1:]
        try:
            if not self.children[input].label == o:
                raise NonDeterminismError()
            self.children[i][inputs] = outputs
        except KeyError:
            child = _node(self.encoder)
            child.label = o
            self.children[i] = child
            self.encoder._add_trans_constraint(self.name, i, child.name)
            self.encoder._add_out_constraint(self.name, i, o)
            self.children[i][inputs] = outputs

    def __len__(self):
        """Returns the number of nodes in the APT
        (this is not necessarily the number of key, label pairs).
        """
        n = 1
        for key in self.children.keys():
            n = n + len(self.children[key])
        return n

    def count_labels(self):
        """Returns the number of key, label pairs in the APT."""
        n = 1 if self.label != None else 0
        for key in self.children.keys():
            n = n + count_labels(self.children[key])
        return n
