import itertools
from abc import ABCMeta, abstractmethod
from types import GeneratorType
from typing import List, Generator, Iterable, Tuple

from model import Automaton, Acceptor, Transducer
from model.fa import MealyMachine, Symbol
from model.ra import IORegisterAutomaton, Action
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

class TestGenerator(metaclass=ABCMeta):
    @abstractmethod
    def gen_test(self, model: Automaton) -> Test:
        """generates a Test. Returns None if the test suite is exhausted"""
        pass

    def gen_test_iter(self, model: Automaton) -> Iterable[Test]:
        test = self.gen_test(model)
        while test is not None:
            yield test
            test = self.gen_test(model)

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
        while True:
            test = self.generator.gen_test(model)
            if test is None:
                return None
            trace = test.check(model)
            if trace is not None:
                return trace


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

    def size(self):
        return len(self.tr)

class MealyTest(TransducerTest):
    def __init__(self, trace:List[Tuple[Symbol, Symbol]]):
        super().__init__(trace)

class IORATest(TransducerTest):
    def __init__(self, trace: List[Tuple[Action, Action]]):
        super().__init__(trace)

    def _check_trace(self, model: IORegisterAutomaton, trace: List[Tuple[Action, Action]]):
        # any observation trace has to be first determinized
        trace = determinize_act_io(trace)
        return super()._check_trace(model, trace)


# Acceptor Test observations are tuples comprising sequences of Actions/Symbols joined by an accept/reject booleans
class AcceptorTest(Test):
    def __init__(self, trace:Tuple[List[object], bool]):
        super().__init__(trace)

    def _check_trace(self, model: Acceptor, trace):
        test_trace = []
        (seq, acc) = trace
        if model.accepts(seq) is not acc:
            return test_trace
        return None

    def size(self):
        (seq, acc) = self.tr
        return len(seq)