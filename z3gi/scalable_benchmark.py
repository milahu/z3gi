import functools
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
from sut import SUTType, StatsSUT, DFAObservation, RAObservation, MealyObservation, IORAObservation
from sut.login import LoginClass
from sut.scalable import ScalableSUTClass
from sut.fifoset import FIFOSetClass
from sut.stack import StackClass
from sut.sut_cache import AcceptorCache, IOCache, CacheSUT
from learn.algorithm import learn_mbt, Statistics
from test.chain import TestGeneratorChain
from test.coloring import ColoringTestGenerator
from test.rwalk import DFARWalkFromState, MealyRWalkFromState, RARWalkFromState, IORARWalkFromState
from statistics import stdev, median

# dirty benchmark module for scalable systems
class SutDesc(collections.namedtuple("SutDesc", 'sut_class type size')):
    def __str__(self):
        return  str(self.type).replace("SUTType.","") + "_" + str(self.sut_class.__class__.__name__).replace("Class", "") + "(" + str(self.size) + ")"

TestDesc = collections.namedtuple("TestDesc", 'max_tests rand_length prop_reset')
class ExperimentStats(collections.namedtuple("CollectedStats", "states minimal registers tests "
                                                              "inputs max_ltime learn_time")):
    pass

class CollatedStats(collections.namedtuple("CollatedStats", "exp_succ states registers minimal consistent avg_tests std_tests avg_inputs std_inputs max_ltime avg_ltime std_ltime")):
    pass

def get_learner_setup(sut, sut_type:SUTType, size, test_desc:TestDesc):
    args = (sut, test_desc.rand_length+size, test_desc.prop_reset)
    if sut_type is SUTType.DFA:
        return (FALearner(DFAEncoder()), DFARWalkFromState(*args))
    elif sut_type is SUTType.Mealy:
        return (FALearner(MealyEncoder()), MealyRWalkFromState(*args))
    elif sut_type is SUTType.RA:
        ra_learner = RALearner(RAEncoder())
        ra_learner.set_num_reg(size)
        return (ra_learner, RARWalkFromState(*args))
    elif sut_type is SUTType.IORA:
        ra_learner = RALearner(IORAEncoder())
        ra_learner.set_num_reg(size)
        return (ra_learner, IORARWalkFromState(*args))
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

    def _run_benchmark(self, sut_class:ScalableSUTClass, sut_type:SUTType, test_desc:TestDesc, tout:int,\
                       min_size:int, max_size:int, use_coloring:bool) -> List[Tuple[SutDesc, ExperimentStats]]:
        results = []
        size = min_size
        while True:
            if max_size is not None and size > max_size:
                break
            print("Learning ", size)
            sut = sut_class.new_sut(sut_type, size)
            stats_sut = StatsSUT(sut)
            sut_stats = stats_sut.stats_tracker()

            if sut_type.is_acceptor():
                if sut_type is SUTType.DFA:
                    cache = AcceptorCache(DFAObservation)
                else:
                    cache = AcceptorCache(RAObservation)
            else:
                if sut_type is SUTType.Mealy:
                    cache = IOCache(MealyObservation)
                else:
                    cache = IOCache(IORAObservation)
            cache_sut = CacheSUT(stats_sut, cache)
            learner,tester = get_learner_setup(cache_sut, sut_type, size, test_desc)
            if use_coloring:
                tester = TestGeneratorChain([ColoringTestGenerator(cache_sut, cache), tester])

            learner.set_timeout(tout)
            (model, statistics) = learn_mbt(cache_sut, learner, tester, test_desc.max_tests, stats_tracker=sut_stats)
            if model is None:
                break
            else:
                sut_desc = SutDesc(sut_class, sut_type, size)
                imp_stats = self._collect_stats(sut_desc, model, statistics)
                results.append( (sut_desc, imp_stats))
                size += 1
        return  results

    def _collect_stats(self, sut_desc:SutDesc, model:Automaton, statistics:Statistics) -> ExperimentStats:
        states = len(model.states())
        registers = len(model.registers()) if isinstance(model, RegisterMachine) else None
        exp_size =  sut_desc.sut_class.num_states(sut_desc.type, sut_desc.size)
        minimal = None if exp_size is None else exp_size == len(model.states())
        learn_tests = statistics.resets
        learn_inputs = statistics.inputs
        learn_time = sum(statistics.learning_times)
        max_ltime = max(statistics.learning_times)
        return ExperimentStats(states=states, minimal=minimal, registers=registers, tests=learn_tests, inputs=learn_inputs, max_ltime=max_ltime, learn_time=learn_time)

    def run_benchmarks(self, test_desc:TestDesc, timeout:int, min_size:int=1, max_size:int=1, use_coloring:bool=False) -> List[Tuple[SutDesc, ExperimentStats]]:
        results = []
        for sut_class, sut_type in self.suts:
            res = self._run_benchmark(sut_class, sut_type, test_desc, timeout, min_size, max_size, use_coloring)
            results.extend(res)
        return results

def collate_stats(sut_desc: SutDesc, exp_stats:List[ExperimentStats]):
    if exp_stats is None:
        return None
    else:
        states = [e.states for e in exp_stats]
        avg_states = median(states)
        regs = [e.registers for e in exp_stats]
        if sut_desc.type.has_registers():
            avg_reg = median(regs)
        else:
            avg_reg = None
        if sut_desc.sut_class.num_states(sut_desc.type, sut_desc.size) is None:
            minimal = None
        else:
            minimal = functools.reduce(lambda x,y: x & y, [e.minimal for e in exp_stats])
        consistent = len(set(states)) == 1 and \
        (not sut_desc.type.has_registers() or len(set(regs)) == 1)
        exp_succ = len(exp_stats)
        ltests = [e.tests for e in exp_stats]
        linputs = [e.inputs for e in exp_stats]
        ltime = [e.learn_time for e in exp_stats]
        maxltimes = [e.max_ltime for e in exp_stats]
        return CollatedStats(
            exp_succ=exp_succ,
            states=avg_states,
            registers=avg_reg,
            minimal=minimal,
            consistent=consistent,
            avg_tests=median(ltests),
            std_tests=0 if len(ltests) == 1 else stdev(ltests),
            avg_inputs=median(linputs),
            std_inputs=0 if len(linputs) == 1 else stdev(linputs),
            max_ltime=max(maxltimes),
            avg_ltime=median(ltime),
            std_ltime=0 if len(ltime) == 1 else stdev(ltime),
        )



def print_results(results : List[Tuple[SutDesc, ExperimentStats]]):
    if len(results) == 0:
        print ("No statistics to report on")
    else:
        for sut_desc,stats in results:
            print(sut_desc, " ", stats)

b = Benchmark()

# add the sut classes we want to benchmark (and optionally the types)
b.add_sut(LoginClass())
b.add_sut(FIFOSetClass())
b.add_sut(StackClass())

# create a test description
t_desc = TestDesc(max_tests=10000, prop_reset=0.2, rand_length=3)

# give an smt timeout value (in ms)
timeout = 10000

# how many times each experiment should be run
num_exp = 20

# the start size
min_size = 1

# up to what systems of what size do we want to run experiments (set to None if size is ignored as a stop condition)
max_size = None

# do you want to augment test generation by coloring (before the rwalk, we explore all uncolored transitions in the hyp)
use_coloring = False

# run the benchmark and collect results
results = []
for i in range(0, num_exp):
    results += b.run_benchmarks(t_desc, timeout, min_size, max_size, use_coloring)
    print("============================")
    print_results(results)
    sut_dict = dict()
    for sut_desc,exp in results:
        if sut_desc not in sut_dict:
            sut_dict[sut_desc] = list()
        sut_dict[sut_desc].append(exp)

    collated_stats = [(sut_desc, collate_stats(sut_desc, experiments)) for sut_desc, experiments in sut_dict.items()]
    for (sut_desc, c_stat) in collated_stats:
        print(sut_desc, " ", c_stat)

# print results
print_results(results)

sut_dict = dict()
for sut_desc,exp in results:
    if sut_desc not in sut_dict:
        sut_dict[sut_desc] = list()
    sut_dict[sut_desc].append(exp)

collated_stats = [(sut_desc, collate_stats(sut_desc, experiments)) for sut_desc, experiments in sut_dict.items()]
for (sut_desc, c_stat) in collated_stats:
    print(sut_desc, " ", c_stat)


