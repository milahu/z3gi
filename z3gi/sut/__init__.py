from abc import ABCMeta, abstractmethod
from typing import List, Tuple, Dict

import collections

from model.fa import Symbol
from model.ra import Action
from enum import Enum

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

    def trace(self) -> List[Tuple[Action, Action]]:
        return self.tr

    def inputs(self):
        return [a for (a,_) in self.tr]

    def values(self):
        iv = [a.value for (a,_) in self.tr if a.value is not None]
        ov = [a.value for (_,a) in self.tr if a.value is not None]
        return set(iv+ov)

    def __str__(self):
        return "Obs: " + str(self.tr)

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
    """for a class of systems (say stacks, or logins) provides means of instantiating SUTs of different types"""

    @abstractmethod
    def new_sut(self, sut_type : SUTType) -> SUT:
        """ builds a new SUT of the specified type. Returns None is no such SUT can be generated"""
        pass

class ScalableSUTClass(SUTClass, metaclass=ABCMeta):
    """provides instantiation for scalable SUTs. Scalable SUTs are classes whose constructor take a size >0 integer
    as an argument. This class also adds wrappers corresponding to the type (all SUTs are assumed to be ObjectSULs)."""

    def __init__(self, sut_type_dict:Dict[SUTType,type]):
        self.sut_type_dict = sut_type_dict

    def new_sut(self, sut_type : SUTType, size :int):
        if sut_type in self.sut_type_dict:
            sut_obj = self.sut_type_dict[sut_type](size)
            sut = sut_obj if sut_type is SUTType.IORA else \
                RAWrapper(sut_obj) if sut_type is SUTType.RA else \
                MealyWrapper(sut_obj) if sut_type is SUTType.Mealy else \
                DFAWrapper(MealyWrapper(sut_obj)) if sut_type is SUTType.DFA else \
                    None # no support for Moore Machines (yet)
            return sut
        else:
            return None

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
    """Wraps around an object and calls methods on it corresponding to the Actions.
        IORA is the natural formalism for describing practical SUTs. Depending on the SUT characteristics,
        we can also describe them using less expressing formalisms."""
    def __init__(self, act_sigs, obj_gen):
        self.obj_gen = obj_gen
        self.acts = {act_sig.label:act_sig for act_sig in act_sigs}

    def run(self, seq:List[Action]) -> IORAObservation:
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
            return Action(SUT.OK if outp else SUT.NOK, fresh)
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


class RAWrapper(RASUT):
    """Wraps around a Object SUT and creates an RA view of it. Generates accepting observations only for IORA
    observations ending in SUT.OK outputs or for the empty sequence of inputs. """
    def __init__(self, sut:ObjectSUT):
        self.sut = sut

    def run(self, seq: List[Action]):
        if len(seq) == 0:
            return RAObservation(seq, True)
        else:
            iora_obs = self.sut.run(seq)
            seq = iora_obs.inputs()
            trace = iora_obs.trace()
            (_, out) = trace[-1]
            acc = out.label is SUT.OK
            return RAObservation(seq, acc)


class MealyWrapper(SUT):
    """Wraps around an Object SUT and creates an Mealy view of it. Values in output actions are ignored
    and only the labels are returned. """

    def __init__(self, sut: ObjectSUT):
        self.sut = sut

    def run(self, seq: List[Symbol]) -> MealyObservation:
        iora_seq = [Action(inp, None) for inp in seq]
        iora_obs = self.sut.run(iora_seq)
        mealy_trace = [(inp_act.label, out_act.label) for (inp_act, out_act) in iora_obs.trace()]
        return MealyObservation(mealy_trace)

    def input_interface(self) -> List[Symbol]:
        labels = [action.label for action in self.sut.input_interface()]
        return labels

class DFAWrapper(SUT):
    """Wraps around a Mealy SUT and creates DFA view of it. Traces ending with the SUT.OK output generate accepting
    observations, as does the empty trace. All others generate rejecting observations"""

    def __init__(self, sut: MealyWrapper):
        self.sut = sut

    def run(self, seq: List[Symbol]) -> DFAObservation:
        if len(seq) == 0:
            return DFAObservation(seq, True)
        else:
            mealy_obs = self.sut.run(seq)
            (_,out) = mealy_obs[-1]
            acc = out is SUT.OK
            return DFAObservation(seq, acc)