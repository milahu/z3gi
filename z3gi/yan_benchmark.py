from abc import ABCMeta
from typing import Tuple, List, Dict

import collections

from encode.fa import DFAEncoder, MealyEncoder
from learn import Learner
from learn.fa import FALearner
from model import Automaton
from model.ra import RegisterMachine
from parse.importer import build_automaton_from_dot
from sut import SUTType, get_simulation, MealyObservation, StatsSUT, StatsTracker
from learn.algorithm import learn_mbt, Statistics
from statistics import stdev, median
import os.path

from sut.sut_cache import CacheSUT, IOCache
from test.yanna import YannakakisTestGenerator

TestDesc = collections.namedtuple("TestDesc", 'max_tests max_k rand_length')
ExpDesc = collections.namedtuple("ExpDesc", 'model_name num_states')
class ExperimentStats(collections.namedtuple("CollectedStats", "states registers ces tests inputs learn_time")):
    pass

class CollatedStats(collections.namedtuple("CollatedStats", "exp_succ states consistent avg_tests std_tests avg_inputs std_inputs avg_ltime std_ltime")):
    pass

ModelDesc = collections.namedtuple("ModelDesc", 'name type path')

def get_learner_setup(aut:Automaton, test_desc:TestDesc):
    sut = get_simulation(aut)
    stats_sut = StatsSUT(sut)
    sut_stats = stats_sut.stats_tracker()
    sut = CacheSUT(stats_sut, IOCache( MealyObservation))
    learner = FALearner(MealyEncoder())
    tester = YannakakisTestGenerator(sut, max_k=test_desc.max_k, rand_length=test_desc.rand_length)
    return (learner, tester, sut, sut_stats)

class Benchmark:
    def __init__(self):
        self.model_desc: List[ModelDesc] = []


    def add_experiment(self, mod_desc:ModelDesc):
        self.model_desc.append(mod_desc)
        return self

    def _run_benchmark(self, mod_desc:ModelDesc, test_desc:TestDesc, tout:int) \
            -> List[Tuple[ExpDesc, ExperimentStats]]:
        results = []
        aut = build_automaton_from_dot(mod_desc.type, mod_desc.path)
        (learner, tester, sut, sut_stats) = get_learner_setup(aut, test_desc)
        learner.set_timeout(tout)
        (model, statistics) = learn_mbt(learner, tester, test_desc.max_tests, stats_tracker=sut_stats)
        exp_desc = ExpDesc(mod_desc.name, len(aut.states()))
        if model is not None:
            imp_stats = self._collect_stats(model, statistics)
            results.append( (exp_desc, imp_stats))
        return  results

    def _collect_stats(self, model:Automaton, stats:Statistics) -> ExperimentStats:
        states = len(model.states())
        registers = len(model.registers()) if isinstance(model, RegisterMachine) else None
        return ExperimentStats(states=states,
                               registers=registers,
                               inputs=stats.inputs,
                               tests=stats.resets,
                               ces=len(stats.learning_times),
                               learn_time=sum(stats.learning_times))

    def run_benchmarks(self, test_desc:TestDesc, timeout:int) -> List[Tuple[ExpDesc, ExperimentStats]]:
        results = []
        for mod_desc in self.model_desc:
            res = self._run_benchmark(mod_desc, test_desc, timeout)
            results.extend(res)
        return results

def collate_stats(sut_desc: ExpDesc, exp_stats:List[ExperimentStats]):
    if exp_stats is None:
        return None
    else:
        states = [e.states for e in exp_stats]
        avg_states = median(states)
        consistent = len(set(states)) == 1
        exp_succ = len(exp_stats)
        tests = [e.tests for e in exp_stats]
        inputs = [e.inputs for e in exp_stats]
        time = [e.learn_time for e in exp_stats]
        return CollatedStats(
            exp_succ=exp_succ,
            states=avg_states,
            consistent=consistent,
            avg_tests=median(tests),
            std_tests=0 if len(tests) == 1 else stdev(tests),
            avg_inputs=median(inputs),
            std_inputs=0 if len(inputs) == 1 else stdev(inputs),
            avg_ltime=median(time),
            std_ltime=0 if len(time) == 1 else stdev(time),
        )


#"exp_succ states registers consistent "
#                                                          "avg_ltests std_ltests avg_inputs std_inputs "
#                                                          "avg_ltime std_ltime"

def print_results(results : List[Tuple[ExpDesc, ExperimentStats]]):
    if len(results) == 0:
        print ("No statistics to report on")
    else:
        for sut_desc,stats in results:
            print(sut_desc, " ", stats)

b = Benchmark()

# adding learning setups for each type of machine
# no longer used, built function which returns tuple
models_path = os.path.join("..", "resources", "models")
bankcards_path = os.path.join(models_path, "bankcards")
pdu_path = os.path.join(models_path, "pdu")

biometric = ModelDesc("biometric", "MealyMachine", os.path.join(models_path, "biometric.dot"))
bankard_names= ["MAESTRO", "MasterCard", "PIN", "SecureCode"]

bankcards = [ModelDesc(name, "MealyMachine", os.path.join(bankcards_path, "{}.dot".format(name))) for name in bankard_names]
pdus = [ModelDesc("pdu" + str(i), "MealyMachine",
                  os.path.join(pdu_path, "model{}.dot".format(i))) for i in range(1,7)]

#b.add_experiment(biometric)
#for bankard in bankcards:
#    b.add_experiment(bankard)
#for pdu in pdus:
#    b.add_experiment(pdu)

b.add_experiment(pdus[5])
# create a test description
t_desc = TestDesc(max_tests=10000, max_k=3, rand_length=3)

# give the smt timeout value (in ms)
timeout = 60

# how many times each experiment should be run
num_exp = 1

# run the benchmark and collect results
results = []
for i in range(0, num_exp):
    results += b.run_benchmarks(t_desc, timeout)
    print("============================")
    print_results(results)
    sut_dict = dict()
    for sut_desc,exp in results:
        if sut_desc not in sut_dict:
            sut_dict[sut_desc] = list()
        sut_dict[sut_desc].append(exp)


# sort according to the sut_desc (the first element)
#results.sort()

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


