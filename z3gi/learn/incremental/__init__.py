from abc import ABCMeta, abstractmethod
from typing import Tuple

import model
import define


class ILearner(metaclass=ABCMeta):
    def __init__(self):
        self.timeout = None

    @abstractmethod
    def add(self, trace):
        pass

    @abstractmethod
    def model(self, old_definition:define.Automaton=None, old_model:model.Automaton=None) \
            -> Tuple[model.Automaton, define.Automaton]:
        """"Infers a minimal model whose behavior corresponds to the traces added so far.
        Returns (None, to) if no model could be obtained where to suggests that learning failed due to
         evaluation timing out"""
        pass

    def set_timeout(self, to):
        """sets the amount of time the solver is given for constructing a hypothesis"""
        self.timeout = to