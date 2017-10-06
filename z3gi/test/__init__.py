from abc import ABCMeta, abstractmethod
from typing import List, Generator, Iterable, Tuple
import itertools

from model import Automaton, Acceptor, Transducer
from model.fa import Symbol
from model.ra import IORegisterAutomaton, Action
from sut import SUT
from sut.scalable import ActionSignature
from utils import determinize


class Test(metaclass=ABCMeta):
    """A test is based on a trace/observation on the actual SUT. The test verifies that
    the model exhibits behavior corresponding to this observation."""
    def __init__(self, trace):
        self.tr = trace

    def check(self, model:Automaton):
        """checks if the hyp passes the test. On failure, it returns a minimal trace to be added by the learner.
        On success it return None"""
        return self._check_trace(model, self.tr)

    @abstractmethod
    def _check_trace(self, model, trace):
        pass

    def trace(self):
        """returns the trace/observation of the SUT the Test is based on"""
        return self.tr

    @abstractmethod
    def size(self) -> int:
        """returns the size (in terms of inputs) of the test"""
        pass

    @abstractmethod
    def covers(self, test) -> bool:
        pass

class EqualTestsMixin(metaclass=ABCMeta):
    """doesn't work unfortunately"""
    def __eq__(self, other):
        return other and  type(other) is type(self) and other.tr == self.tr

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash((type(self), frozenset(self.tr)))



class TestGenerator(metaclass=ABCMeta):
    #TODO gen_test should take the sut as param (relieving the testgens of having to store it in a field)
    @abstractmethod
    def gen_test(self, model: Automaton) -> Test:
        """generates a Test. Returns None if the test suite is exhausted"""
        pass

    def gen_test_iter(self, model: Automaton) -> Iterable[Test]:
        self.initialize(model)
        test = self.gen_test(model)
        while test is not None:
            yield test
            test = self.gen_test(model)
        self.terminate()

    def gen_blind_inp_seq(self, sut:SUT):
        """generates a sequence covering all input elements in the sut interface"""
        seq = []
        for abs_inp in self.sut.input_interface():
            cnt = 0
            # if it's RA stuff
            if isinstance(abs_inp, ActionSignature):
                if abs_inp.num_params == 0:
                    val = None
                else:
                    val = cnt
                    cnt += 1
                seq.append(Action(abs_inp.label, val))
            elif isinstance(abs_inp, str):
                seq.append(abs_inp)
            else:
                raise Exception("Unrecognized type")
        return seq

    def initialize(self, model: Automaton):
        """feeds the tests generator the supplied automaton in an initialization step"""
        pass

    def terminate(self):
        pass

class TracesGenerator(metaclass=ABCMeta):
    def __init__(self, traces = list()):
        self.traces = traces

    def gen_test(self, model:Automaton):
        if len(self.traces) > 0:
            return self.traces.pop(0)
        return None

class Tester(metaclass=ABCMeta):
    def __init__(self, test_generator:TestGenerator):
        self.generator = test_generator

    def find_ce(self, model:Automaton):
        """generates an observation which exposes a counterexample"""
        self.generator.initialize(model)
        ce = None
        while True:
            test = self.generator.gen_test(model)
            if test is None:
                break
            trace = test.check(model)
            if trace is not None:
                ce = trace
                break
        self.generator.terminate()


def determinize_act_io(tuple_seq):
    seq = list(itertools.chain.from_iterable(tuple_seq))
    det_seq = determinize(seq)
    det_act_seq = [Action(l, v) for (l, v) in det_seq]
    det_duple_seq = [(det_act_seq[i], det_act_seq[i + 1]) for i in range(0, len(det_act_seq), 2)]
    return det_duple_seq

class TransducerTest(Test):
    def __init__(self, trace:List[Tuple[object, object]]):
        super().__init__(trace)

    def _check_trace(self, model: Transducer, trace:List[Tuple[object, object]]):
        test_trace = []
        for (inp_act, out_act) in trace:
            test_trace.append((inp_act, out_act))
            output = model.output([inp for (inp, _) in test_trace])
            if output != out_act:
                return  test_trace
        return None

    def __hash__(self):
        return hash((type(self), frozenset(self.tr)))

    def __eq__(self, other):
        return other and type(other) is type(self) and other.tr == self.tr

    def __ne__(self, other):
        return not self.__eq__(other)

    def size(self):
        return len(self.tr)

    def covers(self, test):
        if type(test) is type(self) and len(test.trace()) <= len(self.trace()):
            for ((inp, _),(inp2, _)) in zip(self.trace(), test.trace()):
                if inp != inp2:
                    return  False
            return True
        return False


class MealyTest(TransducerTest):
    def __init__(self, trace:List[Tuple[Symbol, Symbol]]):
        super().__init__(trace)

    def __eq__(self, other):
        return super().__eq__(other)

    def __ne__(self, other):
        return super().__ne__(other)

    def __hash__(self):
        return super().__hash__()

class IORATest(TransducerTest):
    def __init__(self, trace: List[Tuple[Action, Action]]):
        super().__init__(trace)

    def _check_trace(self, model: IORegisterAutomaton, trace: List[Tuple[Action, Action]]):
        # any observation trace has to be first determinized
        trace = determinize_act_io(trace)
        return super()._check_trace(model, trace)

    def __eq__(self, other):
        return super().__eq__(other)

    def __ne__(self, other):
        return super().__ne__(other)

    def __hash__(self):
        return super().__hash__()

# Acceptor Test observations are tuples comprising sequences of Actions/Symbols joined by an accept/reject booleans
class AcceptorTest(Test):
    def __init__(self, trace:Tuple[List[object], bool]):
        super().__init__(trace)

    def _check_trace(self, model: Acceptor, trace):
        (seq, acc) = trace
        if model.accepts(seq) != acc:
            return trace
        return None

    def size(self):
        (seq, acc) = self.tr
        return len(seq)

    def __hash__(self):
        (seq, acc) = self.tr
        return hash((type(self), frozenset(seq), acc))

    def __eq__(self, other):
        return other and type(other) is type(self) and other.tr == self.tr

    def __ne__(self, other):
        return not self.__eq__(other)

    def covers(self, test):
        if type(test) is type(self) and self.size() <= test.size():
            (seq, _) =  self.trace()
            (seq2, _) = test.trace()
            return seq == seq2
        return False

