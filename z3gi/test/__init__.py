import itertools
from abc import ABCMeta, abstractmethod
from typing import List

from model import Automaton, Acceptor
from model.fa import MealyMachine
from model.ra import IORegisterAutomaton, Action
from utils import determinize


class Test(metaclass=ABCMeta):

    @abstractmethod
    def check(self, model:Automaton):
        """checks if the hyp passes the test. On failure, it returns the trace to be added by the learner.\
        On success it return None"""
        pass


class TestTemplate(metaclass=ABCMeta):
    def __init__(self, trace):
        self.trace = trace

    def check(self, model: Automaton):
        return self._check_trace(model, self.trace)

    @abstractmethod
    def _check_trace(self, model, trace):

        pass


    @abstractmethod
    def size(self) -> int:
        """Returns the size (in terms of inputs) of the test"""
        pass


class TestGenerator(metaclass=ABCMeta):
    @abstractmethod
    def gen_test(self, model: Automaton) -> Test:
        """generates a Test. Returns None if the test suite is exhausted"""
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
        while True:
            test = self.generator.gen_test(model)
            if test is None:
                return None
            trace = test.check(model)
            if trace is not None:
                return trace

# IORA Test traces are sequences of input and output action tuples
# (Action("in", 10), Action("out", 11))

class IORATest(TestTemplate):
    def __init__(self, trace:List[tuple]):
        super().__init__(trace)

    def _check_trace(self, model: IORegisterAutomaton, trace:List[tuple]):
        test_trace = []
        trace = determinize_act_io(trace)
        for (inp_act, out_act) in trace:
            test_trace.append((inp_act, out_act))
            if inp_act.label not in model.input_labels():
                return test_trace
            output = model.output([inp for (inp, _) in test_trace])
            if output != out_act:
                return  test_trace
        return None

    def size(self):
        return len(self.trace)



def determinize_act_io(tuple_seq):
    seq = list(itertools.chain.from_iterable(tuple_seq))
    det_seq = determinize(seq)
    det_act_seq = [Action(l, v) for (l, v) in det_seq]
    det_duple_seq = [(det_act_seq[i], det_act_seq[i + 1]) for i in range(0, len(det_act_seq), 2)]
    return det_duple_seq


class MealyTest(TestTemplate):
    def __init__(self, trace:List[tuple]):
        super().__init__(trace)

    def _check_trace(self, model: MealyMachine, trace:List[tuple]):
        test_trace = []
        for (inp_act, out_act) in trace:
            test_trace.append((inp_act, out_act))
            output = model.output([inp for (inp, _) in test_trace])
            if output != out_act:
                return  test_trace
        return None

    def size(self):
        return len(self.trace)

# Acceptor Test observations are tuples comprising sequences of Actions/Symbols joined by an accept/reject booleans
class AcceptorTest(TestTemplate):
    def __init__(self, trace):
        super().__init__(trace)

    def _check_trace(self, model: Acceptor, trace):
        test_trace = []
        (seq, acc) = trace
        if model.accepts(seq) is not acc:
            return test_trace
        return None

    def size(self):
        (seq, acc) = self.trace
        return len(seq)