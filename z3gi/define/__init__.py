from abc import ABCMeta, abstractmethod

class Automaton(metaclass=ABCMeta):
    @abstractmethod
    def export(self):
        """Returns a z3gi.model for this automaton."""
        pass