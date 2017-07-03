from abc import ABCMeta, abstractmethod

from model import Automaton


class Learner(metaclass=ABCMeta):
    @abstractmethod
    def add(self, trace):
        pass

    @abstractmethod
    def model(self, old_model=None) -> Automaton:
        """"Infers a minimal model whose behavior corresponds to the traces added so far.
        Returns None if no model could be obtained."""
        pass

