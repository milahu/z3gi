from abc import ABCMeta, abstractmethod
from enum import Enum
from typing import List, Tuple

from model import Automaton
from model.fa import Symbol, MealyMachine
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

from sut.scalable import ScalableSUTClass
from sut.simulation import Simulation, MealyMachineSimulation

def get_scalable_sut(sut_class_name, sut_type, sut_size):
    """builds a scalable sut of the given class, type and size"""
    sut_class = scalable_sut_classes()[sut_class_name]
    sut = sut_class().new_sut(sut_type, sut_size)
    return sut

def scalable_sut_classes():
    """retrieves a dictionary containing available the names of sut classes and their respective class files"""
    sc = dict()
    for subclass in ScalableSUTClass.__subclasses__():
        sc[subclass.__name__.replace("SUTClass","")] = subclass
    return sc

# TODO replace not suported -> print exit by throwing an adequate exception
def get_simulation(aut: Automaton) -> Simulation:
    """builds a simulation for the model. The simulation acts like a deterministic sut."""
    if aut is MealyMachine:
        return MealyMachineSimulation(aut)
    else:
        print("Simulation not yet supported for ", type(aut))
        exit(0)