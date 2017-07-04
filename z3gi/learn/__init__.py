from abc import ABCMeta, abstractmethod
from typing import Tuple

import model
import define


class Learner(metaclass=ABCMeta):
    @abstractmethod
    def add(self, trace):
        pass

    @abstractmethod
    def model(self, old_definition:define.Automaton=None) -> Tuple[model.Automaton, define.Automaton]:
        """"Infers a minimal model whose behavior corresponds to the traces added so far.
        Returns None if no model could be obtained."""
        pass

