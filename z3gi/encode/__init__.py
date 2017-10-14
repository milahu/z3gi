from abc import ABCMeta, abstractmethod

import z3
from define import Automaton

class Encoder(metaclass=ABCMeta):
    @abstractmethod
    def add(self, trace) -> None:
        pass

    @abstractmethod
    def build(self, *args) -> (Automaton, z3.ExprRef):
        pass

# an encoder which builds trace and automaton constraints independently from each other. This allows Learners to use incremental
# solving algorithms
# TODO build incremental encoders and learners
class IncrementalEncoder(metaclass=ABCMeta):
    @abstractmethod
    def add(self, trace) -> None:
        pass

    @abstractmethod
    def transitions(self):
        pass

    @abstractmethod
    def automaton(self, *args):
        pass