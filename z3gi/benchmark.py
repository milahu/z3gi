from abc import ABCMeta
from typing import Tuple, List, Dict

import collections

from encode.fa import DFAEncoder, MealyEncoder
from encode.iora import IORAEncoder
from encode.ra import RAEncoder
from learn import Learner
from learn.fa import FALearner
from learn.ra import RALearner
from model import Automaton
from model.ra import RegisterMachine
from sut import SUTType, ScalableSUTClass
from sut.fifoset import FIFOSetClass
from sut.login import LoginClass
from test import TestGenerator
from learn.algorithm import learn_mbt, Statistics
from test.rwalk import DFARWalkFromState, MealyRWalkFromState, RARWalkFromState, IORARWalkFromState


class SutDesc(collections.namedtuple("SutDesc", 'sut_class type size')):
    def __str__(self):
        return  str(self.type).replace("SUTType.","") + "_" + str(self.sut_class.__class__.__name__).replace("Class", "") + "(" + str(self.size) + ")"

TestDesc = collections.namedtuple("TestDesc", 'max_tests rand_length prop_reset')
class CollectedStats(collections.namedtuple("CollectedStats", "states registers learn_tests "
                                                              "learn_inputs total_tests learn_time")):
    pass


def get_learner_setup(sut_type:SUTType):
    if sut_type is SUTType.DFA:
        return (FALearner(DFAEncoder()), DFARWalkFromState)
    elif sut_type is SUTType.Mealy:
        return (FALearner(MealyEncoder()), MealyRWalkFromState)
    elif sut_type is SUTType.RA:
        return (RALearner(RAEncoder()), RARWalkFromState)
    elif sut_type is SUTType.IORA:
        return (RALearner(IORAEncoder()), IORARWalkFromState)
    raise Exception("Invalid setup")

class Benchmark:
    def __init__(self):
        self.suts:List[Tuple[ScalableSUTClass, SUTType]] = []
        self.learn_setup: Dict[SUTType, Tuple[Learner, type]] = {}

    def add_sut(self, sut_class:ScalableSUTClass, sut_type=None):
        if sut_type is None:
            for st in list(SUTType):
                if sut_class.new_sut(st, 1) is not None:
                    self.suts.append((sut_class, st))
        else:
            if sut_class.new_sut(sut_type, 1) is None:
                raise Exception(" Added type not implemented by the sut class")
            self.suts.append((sut_class, sut_type))
        return self

    def add_setup(self, sut_type, sut_learner, sut_tester):
        self.learn_setup[sut_type] = (sut_learner, sut_tester)
        return self

    def _run_benchmark(self, sut_class:ScalableSUTClass, sut_type:SUTType, test_desc:TestDesc, tout:int) \
            -> List[Tuple[SutDesc, CollectedStats]]:
        results = []
        size = 1
        while True:
            sut = sut_class.new_sut(sut_type, size)
            learner,test_gen = get_learner_setup(sut_type)
            learner.set_timeout(tout)
            # ugly but there you go
            rand_length = size + test_desc.rand_length
            tester = test_gen(sut, rand_length, test_desc.prop_reset)
            (model, statistics) = learn_mbt(learner, tester, test_desc.max_tests)
            if model is None:
                break
            else:
                imp_stats = self._collect_stats(model, statistics)
                sut_desc = SutDesc(sut_class, sut_type, size)
                results.append( (sut_desc, imp_stats))
                size += 1
        return  results

    def _collect_stats(self, model:Automaton, statistics:Statistics) -> CollectedStats:
        states = len(model.states())
        registers = len(model.registers()) if isinstance(model, RegisterMachine) else None
        learn_tests = statistics.num_learner_tests
        learn_inputs = statistics.num_learner_inputs
        total_tests = statistics.suite_size
        learn_time = sum(statistics.learning_times)
        return CollectedStats(states=states, registers=registers, learn_tests=learn_tests, learn_inputs=learn_inputs,
                              total_tests=total_tests, learn_time=learn_time)

    def run_benchmarks(self, test_desc:TestDesc, timeout:int) -> List[Tuple[SutDesc, CollectedStats]]:
        results = []
        for sut_class, sut_type in self.suts:
            res = self._run_benchmark(sut_class, sut_type, test_desc, timeout)
            results.extend(res)
        return results


def print_results(results : List[Tuple[SutDesc, CollectedStats]]):
    if len(results) == 0:
        print ("No statistics to report on")
    else:
        for sut_desc,stats in results:
            print(sut_desc, " ", stats)


b = Benchmark()

# adding learning setups for each type of machine
# no longer used, built function which returns tuple
#b.add_setup(SUTType.DFA, FALearner(DFAEncoder()), DFARWalkFromState)
#b.add_setup(SUTType.Mealy, FALearner(MealyEncoder()), MealyRWalkFromState)
#b.add_setup(SUTType.RA, RALearner(RAEncoder()), RARWalkFromState)
#b.add_setup(SUTType.IORA, RALearner(IORAEncoder()), IORARWalkFromState)

# add the sut classes we want to benchmark
#b.add_sut(LoginClass(), SUTType.DFA)
b.add_sut(FIFOSetClass(), SUTType.Mealy)

# create a test description
t_desc = TestDesc(max_tests=10000, prop_reset=0.1, rand_length=5)

# give an smt timeout value (in ms)
timeout = 100000

# run the benchmark and collect results
results = b.run_benchmarks(t_desc, timeout)

# print results
print_results(results)



