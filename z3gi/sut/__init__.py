from abc import ABCMeta, abstractmethod
from enum import Enum
from typing import List, Tuple

from model.fa import Symbol
from model.ra import Action

__all__ = [
    "get_simulation",
    "get_scalable_sut",
    "scalable_sut_classes"
    ]

class Observation():
    @abstractmethod
    def trace(self):
        """returns the trace to be added to the solver"""
        pass

    @abstractmethod
    def inputs(self):
        """returns all the inputs from an observation"""
        pass

class TransducerObservation(metaclass=ABCMeta):
    def __init__(self, iotrace:List[Tuple[object,object]]):
        self.iotrace = iotrace

    def trace(self) -> List[Tuple[object,object]]:
        return self.iotrace

    def inputs(self) -> List[object]:
        return [a for (a,_) in self.iotrace]

    def __str__(self):
        return "Obs" + str(self.trace()) + ""

class AcceptorObservation(metaclass=ABCMeta):
    def __init__(self, seq:List[object], acc:bool):
        self.seq = seq
        self.acc = acc

    def trace(self) -> Tuple[List[object], bool]:
        return (self.seq, self.acc)

    def inputs(self) -> List[object]:
        return self.seq

    def __str__(self):
        return "Obs" + str(self.trace())

class DFAObservation(AcceptorObservation):
    def __init__(self, seq, acc):
        super().__init__(seq, acc)

    def trace(self) -> Tuple[List[Symbol], bool]:
        return super().trace()

    def inputs(self) -> List[Symbol]:
        return super().inputs()

class MealyObservation(TransducerObservation):
    def __init__(self, iotrace):
        super().__init__(iotrace)

    def trace(self) -> List[Tuple[Symbol, Symbol]]:
        return super().trace()

    def inputs(self) -> List[Symbol]:
        return super().inputs()

class RegisterMachineObservation(Observation):

    @abstractmethod
    def values(self):
        """returns all the values in the trace"""
        pass



class RAObservation(AcceptorObservation, RegisterMachineObservation):
    def __init__(self, seq, acc):
        super().__init__(seq, acc)

    def trace(self) -> Tuple[List[Action], bool]:
        return self.trace()

    def inputs(self) -> List[Action]:
        return super().inputs()

    def values(self):
        return set([a.value for a in self.inputs() if a.value is not None])

class IORAObservation(TransducerObservation, RegisterMachineObservation):
    def __init__(self, trace):
        super().__init__(trace)

    def trace(self) -> List[Tuple[Action, Action]]:
        return super().trace()

    def inputs(self) -> List[Action]:
        return super().inputs()

    def values(self):
        iv = [a.value for (a,_) in self.trace() if a.value is not None]
        ov = [a.value for (_,a) in self.trace() if a.value is not None]
        return set(iv+ov)

class SUT(metaclass=ABCMeta):
    OK = "OK"
    NOK = "NOK"
    @abstractmethod
    def run(self, seq:List[object]) -> Observation:
        """Runs a sequence of inputs on the SUT and returns an observation"""
        pass

    @abstractmethod
    def input_interface(self) -> List[object]:
        """Runs the list of inputs or input signatures comprising the input interface"""
        pass

class SUTType(Enum):
    IORA = 1
    RA = 2
    Mealy = 3
    Moore = 4
    DFA = 5

    def is_acceptor(self):
        return  self == SUTType.RA or self.DFA

    def has_registers(self):
        return self == SUTType.RA or self == SUTType.IORA

    def is_transducer(self):
        return  not self.is_acceptor()

# some useful functions
from sut.scalable import scalable_sut_classes, get_scalable_sut
from sut.simulation import get_simulation


class StatsTracker(object):
    def __init__(self, sut):
        self.__sut = sut

    def inputs(self):
        return self.__sut._inputs

    def resets(self):
        return self.__sut._resets

class StatsSUT(SUT):
    def __init__(self, sut:SUT):
        self._sut = sut
        self._inputs = 0
        self._resets = 0

    def input_interface(self):
        return self._sut.input_interface()

    def run(self, seq:List[object]):
        self._inputs += len(seq)
        self._resets += 1
        return self._sut.run(seq)

    def stats_tracker(self):
        return StatsTracker(self)



