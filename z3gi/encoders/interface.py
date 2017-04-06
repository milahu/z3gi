class Encoder(object):
    """An Encoder constructs a set of constraints for labeled strings.
    This is an abstract class that provides the interface for an encoder implementation.
    """
    def __setitem__(self, string, label):
        """Adds constraints for a string, label pair."""
        raise NotImplementedError

    def encode(self, n):
        """Returns a list of z3 constraints for a model with n states."""
        raise NotImplementedError

    def __len__(self):
        """Returns the number of encoded string, label pairs."""
        raise NotImplementedError
