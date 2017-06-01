#TODO allow customization for the else branch of z3 functions
#TODO let encoders construct and return these types of models
#TODO put each model in a separate file?
import z3

class Model(object):
    """A Model contains a definition for a model of computation, and provides utility functions for this model.
    This is an abstract class that provides the interface for a model implementation.

    See an implementation for example declaration and usage.
    """
    def __getitem__(self, string):
        """Returns the computation of the provided string on the model.
        Raises a NotAssignedError if the model is not assigned yet.
        Raises a KeyError if string contains an unknown symbol.

        Keyword arguments:
        string -- an iterable of symbol identifiers
        """
        raise NotImplementedError()

    def export(self, f):
        """Writes the model in DOT format to text stream f.
        Raises a NotAssignedError if the model is not assigned yet.
        """
        raise NotImplementedError()

    def assign(self, model):
        """Assigns the model.
        Returns a ModelError if not all the constants, terms and functions of this model's definition can be evaluated on the model's assignment.

        Keyword arguments:
        model -- a z3.ModelRef assignment for the constants, terms and functions in this model
        """
        raise NotImplementedError()

    def assigned(self):
        """Returns True if the model is assigned, and False otherwise."""
        return self.model is None


def is_uninterpreted(x):
    return z3.is_const(x) and x.decl().kind() == z3.Z3_OP_UNINTERPRETED

