from abc import ABCMeta, abstractmethod

import z3
from define import Automaton

# an encoder which builds all constraints necessary.
class Encoder(metaclass=ABCMeta):

    @abstractmethod
    def add(self, trace) -> None:
        pass

    @abstractmethod
    def build(self, *args) -> (Automaton, z3.ExprRef):
        pass

# an encoder which builds trace and automaton constraints separately. This allows Learners to use incremental
# solving algorithms by pushing/popping automaton constraints.
# TODO build incremental encoders and learners
class IncrementalEncoder(metaclass=ABCMeta):

    @abstractmethod
    def trace(self, trace) -> z3.ExprRef:
        pass

    @abstractmethod
    def automaton(self, *args) -> z3.ExprRef:
        pass