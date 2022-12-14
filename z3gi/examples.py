import os.path

from encode.fa import MealyEncoder, DFAEncoder
from encode.incremental.fa import MealyIEncoder, MealyTreeIEncoder
from encode.ra import RAEncoder
from learn.algorithm import learn
from learn.algorithm import learn_mbt
from learn.fa import FALearner
from learn.incremental.fa import FAILearner
from learn.ra import RALearner
from parse.importer import build_automaton_from_dot
from sut import SUTType, MealyObservation, StatsSUT, RAObservation, IORAObservation
from sut.fifoset import FIFOSetClass
from sut.login import new_login_sut, LoginClass
from sut.simulation import MealyMachineSimulation
from sut.sut_cache import IOCache, CacheSUT, AcceptorCache
from test import IORATest, MealyTest
from test.chain import TestGeneratorChain
from test.coloring import ColoringTestGenerator
from test.rwalk import IORARWalkFromState, MealyRWalkFromState, DFARWalkFromState, RARWalkFromState
from test.yanna import YannakakisTestGenerator
from tests.iora_testscenario import *
from encode.iora import IORAEncoder

# this module gives examples of simple routines for learning models actively or from traces

# some paths
yan_cmd = os.path.join("..","resources", "binaries", "yannakakis.exe")
models_loc = os.path.join("..","resources", "models")
maestro = os.path.join(models_loc, "bankcards", "MAESTRO.dot")
visa = os.path.join(models_loc, "bankcards", "VISA.dot")
biometric = os.path.join(models_loc, "biometric.dot")

# some example runs
def scalable_learn_iora():
    learner = RALearner(IORAEncoder())
    test_type = IORATest
    exp = sut_m5
    (model, statistics) = learn(learner, test_type, exp.traces)
    print(model)
    print(statistics)

def scalable_learn_mbt_iora():
    learner = RALearner(IORAEncoder())
    learner.set_timeout(10000)
    sut = new_login_sut(1)
    mbt = IORARWalkFromState(sut, 5, 0.2)
    (model, statistics) = learn_mbt(sut,learner, mbt, 10000)
    print(model)
    print(statistics)

def scalable_learn_mbt_mealy():
    learner = FALearner(MealyEncoder())
    learner.set_timeout(1000)
    login = LoginClass()
    sut = login.new_sut(SUTType.Mealy, 2)
    mbt = MealyRWalkFromState(sut, 5, 0.2)
    (model, statistics) = learn_mbt(sut,learner, mbt, 10000)
    print(model)
    print(statistics)

def scalable_learn_mbt_dfa():
    learner = FALearner(DFAEncoder())
    learner.set_timeout(100000)
    login = LoginClass()
    sut = login.new_sut(SUTType.DFA, 2)
    mbt = DFARWalkFromState(sut, 5, 0.2)
    (model, statistics) = learn_mbt(sut,learner, mbt, 10000)
    print(model)
    print(statistics)

def scalable_learn_mbt_ra():
    learner = RALearner(RAEncoder())
    learner.set_timeout(600000)
    login = FIFOSetClass()
    sut = login.new_sut(SUTType.RA, 1)
    mbt = RARWalkFromState(sut, 5, 0.2)
    (model, statistics) = learn_mbt(sut,learner, mbt, 10000)
    print(model)
    print(statistics)

def sim_learn_mbt_yan_mealy(dot_path):
    learner = FALearner(MealyEncoder())
    learner.set_timeout(10000)
    dot_aut = build_automaton_from_dot("MealyMachine", dot_path)
    dot_sut = MealyMachineSimulation(dot_aut)
    stats_sut = StatsSUT(dot_sut)
    cache = IOCache(MealyObservation)
    cache_sut = CacheSUT(stats_sut, cache)
    mbt = YannakakisTestGenerator(cache_sut, yan_cmd, seed=1)
    (model, statistics) = learn_mbt(cache_sut, learner, mbt, 10000, stats_tracker=stats_sut.stats_tracker())
    print(model)
    print(statistics)

def sim_learn_mbt_coloryan_mealy(dot_path):
    learner = FALearner(MealyEncoder())
    learner.set_timeout(10000)
    dot_aut = build_automaton_from_dot("MealyMachine", dot_path)
    dot_sut = MealyMachineSimulation(dot_aut)
    stats_sut = StatsSUT(dot_sut)
    cache = IOCache(MealyObservation)
    cache_sut = CacheSUT(stats_sut, cache)
    mbt1 = ColoringTestGenerator(cache_sut, cache)
    mbt2 = YannakakisTestGenerator(cache_sut, yan_cmd, seed=1)
    mbt = TestGeneratorChain([mbt1, mbt2])
    (model, statistics) = learn_mbt(cache_sut,learner, mbt, 10000, stats_tracker=stats_sut.stats_tracker())
    print(model)
    print(statistics)

def sim_inc_learn_mbt_coloryan_mealy(dot_path):
    learner = FAILearner(MealyTreeIEncoder())
    learner.set_timeout(200000)
    dot_aut = build_automaton_from_dot("MealyMachine", dot_path)
    dot_sut = MealyMachineSimulation(dot_aut)
    stats_sut = StatsSUT(dot_sut)
    cache = IOCache(MealyObservation)
    cache_sut = CacheSUT(stats_sut, cache)
    mbt1 = ColoringTestGenerator(cache_sut, cache)
    mbt2 = YannakakisTestGenerator(cache_sut, yan_cmd, seed=1)
    mbt = TestGeneratorChain([mbt1, mbt2])
    (model, statistics) = learn_mbt(cache_sut,learner, mbt, 10000, stats_tracker=stats_sut.stats_tracker())
    print(model)
    print(statistics)

def scalable_learn_mbt_chainrw_iora():
    learner = RALearner(IORAEncoder())
    learner.set_timeout(600000)
    login = FIFOSetClass()
    sut = login.new_sut(SUTType.IORA, 1)
    cache = IOCache(IORAObservation)
    cache_sut = CacheSUT(sut, cache)
    mbt = TestGeneratorChain([ColoringTestGenerator(cache_sut, cache), RARWalkFromState(sut, 5, 0.2)])
    (model, statistics) = learn_mbt(cache_sut, learner, mbt, 10000)
    print(model)
    print(statistics)

#scalable_learn_mbt_mealy()
#scalable_learn_mbt_iora()
sim_learn_mbt_yan_mealy(maestro)
#sim_learn_mbt_mealy()
