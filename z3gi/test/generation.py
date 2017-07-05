from abc import ABCMeta, abstractmethod
from typing import List, Tuple

from encode.iora import IORAEncoder
from learn.algorithm import learn
from learn.ra import RALearner
from model.ra import Action
from sut import SUT, ActionSignature, RASUT


# class RAObservation():
#     def __init__(self, trace):
#         self.trace = trace
#
#     def values(self):
#         for
from sut.stack import new_stack_sut
from test import IORATest


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
        val_obs = self._generate_observations([(0,[])], 0, max_depth, max_registers)
        obs = [obs for (_, obs) in val_obs]
        return obs



    def _generate_observations(self, prev_obs, crt_depth, max_depth, max_values):
        if crt_depth > max_depth:
            return []
        else:
            new_obs = []
            for (num_val, obs) in prev_obs:
                for act_sig in self.act_sigs:
                    label = act_sig.label
                    if act_sig.num_params == 1:
                        for i in range(0, min(num_val+1, max_values)):
                            seq = [inp for (inp, _) in obs]
                            seq.append(Action(label, i))
                            new_obs.append((max(num_val+1, i), self.sut.run(seq)))
                    else:
                        seq = [inp for (inp, _) in obs]
                        seq.append(Action(label, None))
                        new_obs.append((num_val, self.sut.run(seq)))

            if crt_depth < max_depth:
                extended_obs = self._generate_observations(new_obs, crt_depth + 1, max_depth, max_values)
                new_obs.extend(extended_obs)
            return  new_obs


stack_sut = new_stack_sut(1)
gen = ExhaustiveRAGenerator(stack_sut)
obs = gen.generate_observations(2)
print("\n".join( [str(obs) for obs in obs]))
learner = RALearner(IORAEncoder())
learn(learner, IORATest, obs)
