from abc import ABCMeta, abstractmethod
from typing import List

import collections

from model.ra import Action


class SUT(metaclass=ABCMeta):
    OK = "OK"
    NOK = "NOK"
    @abstractmethod
    def run(self, seq:List[object]):
        """Runs a sequence of inputs on the SUT and returns an observation"""
        pass

    @abstractmethod
    def input_interface(self) -> List[object]:
        """Runs the list of inputs or input signatures comprising the input interface"""
        pass


ActionSignature = collections.namedtuple("ActionSignature", ('label', 'num_params'))
class RASUT(metaclass=ABCMeta):
    @abstractmethod
    def input_interface(self) -> List[ActionSignature]:
        pass

    @abstractmethod
    def run(self, seq:List[Action]):
        """Runs a sequence of inputs on the SUT and returns an observation"""
        pass

class ObjectSUT(RASUT):
    """Wraps around an object and calls methods on it corresponding to the Actions"""
    def __init__(self, act_sigs, obj_gen):
        self.obj_gen = obj_gen
        self.acts = {act_sig.label:act_sig for act_sig in act_sigs}

    def run(self, seq:List[Action]):
        obj = self.obj_gen()
        values = set()
        out_seq = []
        for (label, val) in seq:
            meth = obj.__getattribute__(label)
            if self.acts[label].num_params == 0:
                outp = meth()
            else:
                values.add(val)
                outp = meth(val)
            outp_action = self.parse_out(outp)
            values.add(outp_action.value)
            out_seq.append(outp_action)
        obs = list(zip(seq, out_seq))
        return obs


    def parse_out(self, outp) -> Action:
        fresh = None
        if isinstance(outp, bool):
            return Action(str(outp), fresh)
        if isinstance(outp, str):
            return Action(outp, fresh)
        if isinstance(outp, int):
            return  Action("int", outp)
        if isinstance(outp, tuple) and len(outp) == 2:
            (lbl, val) = outp
            if isinstance(val, int) and isinstance(lbl, str):
                return Action(lbl, val)
        raise Exception("Cannot process output")

    def input_interface(self) -> List[ActionSignature]:
        return list(self.acts.values())