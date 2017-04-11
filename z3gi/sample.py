import z3
from z3gi.encoders import natural

class Sample(object):
    """A Sample encodes labeled strings, and provides methods to learn a model from these strings."""

    def __init__(self, encoder=natural.Encoder()):
        """Returns a new Sample.

        Keyword arguments:
        encoder -- the encoder to use (default: z3gi.encoders.natural.Encoder())
        """
        self.encoder = encoder
        self.constriants = None # will be set once a model is found
        self.statistics = None # will be set when self.model() is called

    def __setitem__(self, string, label):
        """Adds a string, label pair to the encoder."""
        self.encoder[string] = label

    #TODO getitem (run on model)

    def model(self, solver=z3.Solver(), minstates=1, maxstates=100):
        """Returns a z3 model for the strings in the encoder, or unsat.

        Keyword arguments:
        solver -- the z3 solver to use (default: z3.Solver())
        minstates -- a lower bound for the number of states in the model (default 1)
        maxstates -- an upper bound for the number of states in the model (default 100)
        """
        for n in range(minstates, maxstates):
            constraints = self.encoder.encode(n)
            solver.push()
            solver.add(constraints)
            if solver.check() == z3.sat:
                self.constraints = constraints
                self.statistics = solver.statistics()
                return solver.model()
            solver.pop()
        self.statistics = solver.statistics()
        return z3.unsat

    def __len__(self):
        """Returns the number of key, value pairs in this sample."""
        return len(self.encoder)
