from abc import ABCMeta
from typing import List, Type, Union

from model import Acceptor, Transducer, Automaton
from model.fa import MealyMachine, Symbol
from . import SUT, MealyObservation, TransducerObservation, \
    AcceptorObservation

class Simulation(SUT,metaclass=ABCMeta):
    pass


class AcceptorSimulation(Simulation):
    def __init__(self, model:Acceptor, sut_obs_type:Type[Union[AcceptorObservation]]):
        self.model = model
        self.sut_obs_type = sut_obs_type

    def run(self, seq:List[object]):
        return self.sut_obs_type(seq, self.model.accepts(seq))

# TODO the output functionality should be implemented by simulation classes, not by models
class TransducerSimulation(Simulation, metaclass=ABCMeta):
    def __init__(self, model:Transducer, sut_obs_type:Type[TransducerObservation]):
        self.model = model
        self.sut_obs_type = sut_obs_type

    def run(self, seq:List[object]):
        iotrace = []
        inp_seq = []
        for inp in seq:
            inp_seq.append(inp)
            out = self.model.output(inp_seq)
            iotrace.append((inp, out))
        return self.sut_obs_type(iotrace)

class MealyMachineSimulation(TransducerSimulation):
    def __init__(self, model:MealyMachine):
        super().__init__(model, MealyObservation)

    def run(self, seq:List[Symbol]) -> MealyObservation:
        return super().run(seq)

    def input_interface(self):
        return self.model.input_labels()

# TODO replace not suported -> print exit by throwing an adequate exception
def get_simulation(aut: Automaton) -> Simulation:
    """builds a simulation for the model. The simulation acts like a deterministic sut."""
    if isinstance(aut, MealyMachine):
        return MealyMachineSimulation(aut)
    else:
        print("Simulation not yet supported for ", type(aut))
        exit(0)