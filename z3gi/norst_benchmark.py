import functools
from abc import ABCMeta
from typing import Tuple, List, Dict

import collections

from encode.fa import MealyEncoder
from learn import Learner
from learn.fa import FALearner
from model import Automaton
from model.ra import RegisterMachine
from sut import SUTType
from sut import get_no_rst_simulation
from sut.scalable import ScalableSUTClass
from sut.fifoset import FIFOSetClass
from sut.stack import StackClass
from learn.algorithm import Statistics
from statistics import stdev, median
import learn.algorithm as alg
import model.gen as gen

# dirty benchmark module for systems without resets
class SutDesc(collections.namedtuple("SutDesc", 'type size')):
    def __str__(self):
        return  str(self.type).replace("SUTType.","") + "_" + "(" + str(self.size) + ")"

TestDesc = collections.namedtuple("TestDesc", 'max_inputs')
class ExperimentStats(collections.namedtuple("CollectedStats", "states registers "
                                                              "inputs ces max_ltime learn_time")):
    pass

class CollatedStats(collections.namedtuple("CollatedStats", "exp_succ states registers avg_inputs std_inputs max_ltime avg_ces, avg_ltime std_ltime")):
    pass

class Benchmark:
    def __init__(self):
        self.suts = list()

    def add_sut(self, sut_desc):
        self.suts.append(sut_desc)

    def _run_benchmark(self, sut_desc:SutDesc, test_desc:TestDesc, tout:int,\
                       min_size:int, max_size:int) -> List[Tuple[SutDesc, ExperimentStats]]:
        results = []
        size = min_size
        while True:
            if max_size is not None and size > max_size:
                break
            sut_type = sut_desc.type
            if sut_type is not SUTType.Mealy:
                print("No reset not supported")
            aut = gen.random_mealy(2, 2, size)
            sut = get_no_rst_simulation(aut)
            learner = FALearner(MealyEncoder())
            learner.set_timeout(tout)
            (model, statistics) = alg.learn_no_reset(sut, learner, test_desc.max_inputs)
            if model is None:
                break
            else:
                new_sut_desc = SutDesc(sut_desc.type, size)
                imp_stats = self._collect_stats(new_sut_desc, model, statistics)
                results.append( (new_sut_desc, imp_stats))
                size += 1
        return  results

    def _collect_stats(self, sut_desc:SutDesc, model:Automaton, statistics:Statistics) -> ExperimentStats:
        learn_inputs = statistics.inputs
        learn_time = sum(statistics.learning_times)
        max_ltime = max(statistics.learning_times)
        ces = len(statistics.learning_times)
        return ExperimentStats(states=sut_desc.size, registers=None, inputs=learn_inputs, ces=ces, max_ltime=max_ltime, learn_time=learn_time)

    def run_benchmarks(self, test_desc:TestDesc, timeout:int, min_size:int=1, max_size:int=1) -> List[Tuple[SutDesc, ExperimentStats]]:
        results = []
        for sut_desc in self.suts:
            res = self._run_benchmark(sut_desc, test_desc, timeout, min_size, max_size)
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
        (not sut_desc.type.has_registers() or len(set(regs)) == 1)
        exp_succ = len(exp_stats)
        linputs = [e.inputs for e in exp_stats]
        ltime = [e.learn_time for e in exp_stats]
        maxltimes = [e.max_ltime for e in exp_stats]
        ces = [e.ces for e in exp_stats]
        return CollatedStats(
            exp_succ=exp_succ,
            states=avg_states,
            registers=avg_reg,
            avg_inputs=median(linputs),
            avg_ces=median(ces),
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

# the SUT is currently hard-coded
b.add_sut(SutDesc(type=SUTType.Mealy, size=0))

# create a test description
t_desc = TestDesc(max_inputs=2000)

# give an smt timeout value (in ms)
timeout = 30000

# how many times each experiment should be run
num_exp = 20

# the start sizeg
min_size = 1

# up to what systems of what size do we want to run experiments (set to None if size is ignored as a stop condition)
max_size = None

# run the benchmark and collect results
results = []
for i in range(0, num_exp):
    results += b.run_benchmarks(t_desc, timeout, min_size, max_size)
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


