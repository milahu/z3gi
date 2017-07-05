from abc import ABCMeta, abstractmethod
from typing import List
from sut import SUT, ActionSignature


# class RAObservation():
#     def __init__(self, trace):
#         self.trace = trace
#
#     def values(self):
#         for

class ObservationGeneration(metaclass=ABCMeta):

    @abstractmethod
    def generate_observations(self, max_depth) -> List[object]:
        pass

class ExhaustiveRAGenerator(ObservationGeneration):
    def __init__(self, sut:SUT, act_sigs:List[ActionSignature]):
        self.sut = sut
        self.act_sigs = act_sigs
        for sig in act_sigs:
            if sig.num_params > 1:
                raise Exception("This generator assumes at most one parameter per action")

    def generate_observations(self, max_depth, max_registers=3) -> List[list]:
        return self._generate_observations([0,[]], 0, max_depth, max_registers)

    def _generate_observations(self, prev_obs, crt_depth, max_depth, max_values):
        if crt_depth > max_depth:
            return []
        else:
            new_obs = []
            for (num_val, obs) in prev_obs:
                for act_sig in self.act_sigs:
                    label = act_sig.label
                    if act_sig.num_params == 1:
                        for i in range(0, max(num_val, max_values)):
                            seq = [inp for (inp, _) in obs]
                            seq.append((label, i))
                            new_obs[:-1] = (max(num_val, i), self.sut.run(seq))
                    else:
                        seq = [inp for (inp, _) in obs]
                        seq = seq.append((label, None))
                        new_obs[:-1] = (num_val, self.sut.run(seq))

            if crt_depth < max_depth:
                new_obs.extend(self._generate_observations(new_obs, crt_depth+1, max_depth, max_values))
            return  new_obs

