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