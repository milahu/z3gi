import z3
from z3gi.encoders import natural
class UnsatError(Exception):
    """An UnsatError is raised when no model can be found for the sample.
    This is typically because the maximum number of states is too low,
    or there is non-determinism in the sample.
    """
    pass

class Sample(object):
    """A Sample encodes labeled strings, and provides methods to learn a model from these strings."""

    def __init__(self, encoder=natural.Encoder()):
        """Returns a new Sample.

        Keyword arguments:
        encoder -- the encoder to use (default: z3gi.encoders.natural.Encoder())
        """
        self.encoder = encoder
        self.constriants = None # will be set once a model is found

    def __setitem__(self, string, label):
        """Adds a string, label pair to the encoder."""
        self.encoder[string] = label

    #TODO getitem (run on model)

    def model(self, solver=z3.Solver(), minstates=1, maxstates=100):
        """Returns a Model object for the strings in the encoder.

        Keyword arguments:
        solver -- the z3 solver to use (default: z3.Solver())
        minstates -- a lower bound for the number of states in the model (default 1)
        maxstates -- an upper bound for the number of states in the model (default 100)
        """
        if hasattr(self.encoder, 'k'):
            k = self.encoder.k
            if minstates < k:
                minstates = k

        for n in range(minstates, maxstates):
            constraints, model = self.encoder.encode(n)
            solver.push()
            solver.add(constraints)
            if solver.check() == z3.sat:
                self.constraints = constraints
                model.assign(solver.model())
                return model
            solver.pop()
        raise UnsatError("No model with at most %d states exists for sample %s (statistics: %s)." % (maxstates, self.encoder, solver.statistics()))

    def __len__(self):
        """Returns the number of key, value pairs in this sample."""
        return len(self.encoder)
