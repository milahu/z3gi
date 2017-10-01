from abc import ABCMeta, abstractmethod
from typing import List, Tuple

from model.ra import Action
from sut import RASUT, RegisterMachineObservation, IORAObservation

class ObservationGeneration(metaclass=ABCMeta):

    @abstractmethod
    def generate_observations(self, max_depth) -> List[object]:
        pass

class ExhaustiveRAGenerator(ObservationGeneration):
    def __init__(self, sut:RASUT):
        self.sut = sut
        self.act_sigs = sut.input_interface()
        for sig in self.act_sigs:
            if sig.num_params > 1:
                raise Exception("This generator assumes at most one parameter per action")

    def generate_observations(self, max_depth, max_registers=3) -> List[Tuple[Action, Action]]:
        observations = self._generate_observations([IORAObservation([])], 0, max_depth, max_registers+1)
        print("\n".join([str(obs) for obs in observations]))
        obs_traces = [obs.trace() for obs in observations]
        return obs_traces



    def _generate_observations(self, prev_obs:List[RegisterMachineObservation], crt_depth, max_depth, max_values) \
            -> List[RegisterMachineObservation]:
        if crt_depth > max_depth:
            return []
        else:
            new_obs = []
            for obs in prev_obs:
                num_val = max(obs.values()) + 1 if len(obs.values()) > 0 else 0
                for act_sig in self.act_sigs:
                    label = act_sig.label
                    if act_sig.num_params == 1:
                        for i in range(0, min(num_val+1, max_values)):
                            seq = obs.inputs()
                            seq.append(Action(label, i))
                            new_obs.append(self.sut.run(seq))
                    else:
                        seq = obs.inputs()
                        seq.append(Action(label, None))
                        new_obs.append(self.sut.run(seq))

            if crt_depth < max_depth:
                extended_obs = self._generate_observations(new_obs, crt_depth + 1, max_depth, max_values)
                new_obs.extend(extended_obs)
            return  new_obs
