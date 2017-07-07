from abc import ABCMeta, abstractmethod
from typing import List

import collections

from model.fa import Symbol
from model.ra import Action
from enum import Enum


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

    def is_transducer(self):
        return  not self.is_acceptor()


class SUTClass(metaclass=ABCMeta):
    def __init__(self, sut_dict):
        self.sut_dict = sut_dict

    def get_sut(self, sut_type : SUTType) -> SUT:
        return self.sut_dict[sut_type]

    def has_sut(self, sut_type : SUTType) -> bool:
        return  sut_type in self.sut_dict

ActionSignature = collections.namedtuple("ActionSignature", ('label', 'num_params'))
class RASUT(metaclass=ABCMeta):
    @abstractmethod
    def input_interface(self) -> List[ActionSignature]:
        pass

    @abstractmethod
    def run(self, seq:List[Action]):
        """Runs a sequence of inputs on the SUT and returns an observation"""
        pass

class Observation():
    @abstractmethod
    def trace(self):
        """returns the trace to be added to the solver"""
        pass

    @abstractmethod
    def inputs(self):
        """returns all the inputs from an observation"""
        pass

class DFAObservation():
    def __init__(self, seq, acc):
        self.seq = seq
        self.acc = acc

    def trace(self):
        return (self.seq, self.acc)

    def inputs(self) -> List[Symbol]:
        return self.seq

class MealyObservation():
    def __init__(self, trace):
        self.tr = trace

    def trace(self):
        return self.tr

    def inputs(self) -> List[Symbol]:
        return [a for (a,_) in self.tr]

class RegisterMachineObservation(Observation):

    @abstractmethod
    def values(self):
        """returns all the values in the trace"""
        pass



class RAObservation(RegisterMachineObservation):
    def __init__(self, seq, acc):
        self.seq = seq
        self.acc = acc

    def trace(self):
        return (self.trace, self.acc)

    def inputs(self):
        return self.seq

    def values(self):
        return set([a.value for a in self.seq if a.value is not None])

class IORAObservation(RegisterMachineObservation):
    def __init__(self, trace):
        self.tr = trace

    def trace(self):
        return self.tr

    def inputs(self):
        return [a for (a,_) in self.tr]

    def values(self):
        iv = [a.value for (a,_) in self.tr if a.value is not None]
        ov = [a.value for (_,a) in self.tr if a.value is not None]
        return set(iv+ov)

    def __str__(self):
        return "Obs: " + str(self.tr)




class ObjectSUT(RASUT):
    """Wraps around an object and calls methods on it corresponding to the Actions"""
    def __init__(self, act_sigs, obj_gen):
        self.obj_gen = obj_gen
        self.acts = {act_sig.label:act_sig for act_sig in act_sigs}

    def run(self, seq:List[Action]):
        obj = self.obj_gen()
        values = dict()
        out_seq = []
        for (label, val) in seq:
            meth = obj.__getattribute__(label)
            if self.acts[label].num_params == 0:
                outp = meth()
            else:
                (values, val) = self._res_ival(values, val)
                outp = meth(val)
            (out_label, out_val) = self.parse_out(outp)
            if out_val is not None:
                (values, out_val) = self._res_oval(values, out_val)
            outp_action = Action(out_label, out_val)
            out_seq.append(outp_action)
        obs = list(zip(seq, out_seq))
        return IORAObservation(obs)

    def _res_ival(self, val_dict, val):
        l = [a for a in val_dict.keys() if val_dict[a] == val]
        if len(l) > 1:
            raise Exception("Collision")
        if len(l) == 1:
            return (val_dict, l[0])
        val_dict[val] = val
        return (val_dict, val)

    def _res_oval(self, val_dict, val):
        if val in val_dict:
            return (val_dict, val_dict[val])
        else:
            val_dict[val] = max(val_dict.values()) + 1 if len(val_dict) > 0 else 0
            return (val_dict, val_dict[val])

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