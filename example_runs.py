import itertools

from encode.fa import MealyEncoder, DFAEncoder
from encode.ra import RAEncoder
from learn.algorithm import learn
from learn.algorithm import learn_mbt
from learn.fa import FALearner
from learn.ra import RALearner
from parse.importer import build_automaton_from_dot
from sut import SUTType
from sut.fifoset import FIFOSetClass
from sut.login import new_login_sut, LoginClass
from sut.simulation import MealyMachineSimulation
from test import IORATest
from test.rwalk import IORARWalkFromState, MealyRWalkFromState, DFARWalkFromState, RARWalkFromState
from test.yanna import YannakakisTestGenerator
from tests.iora_testscenario import *
from encode.iora import IORAEncoder

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
    (model, statistics) = learn_mbt(learner, mbt, 10000)
    print(model)
    print(statistics)

def scalable_learn_mbt_mealy():
    learner = FALearner(MealyEncoder())
    learner.set_timeout(1000)
    login = LoginClass()
    sut = login.new_sut(SUTType.Mealy, 2)
    mbt = MealyRWalkFromState(sut, 5, 0.2)
    (model, statistics) = learn_mbt(learner, mbt, 10000)
    print(model)
    print(statistics)

def scalable_learn_mbt_dfa():
    learner = FALearner(DFAEncoder())
    learner.set_timeout(100000)
    login = LoginClass()
    sut = login.new_sut(SUTType.DFA, 2)
    mbt = DFARWalkFromState(sut, 5, 0.2)
    (model, statistics) = learn_mbt(learner, mbt, 10000)
    print(model)
    print(statistics)

def scalable_learn_mbt_ra():
    learner = RALearner(RAEncoder())
    learner.set_timeout(600000)
    login = FIFOSetClass()
    sut = login.new_sut(SUTType.RA, 1)
    mbt = RARWalkFromState(sut, 5, 0.2)
    (model, statistics) = learn_mbt(learner, mbt, 10000)
    print(model)
    print(statistics)

def sim_learn_mbt_mealy():
    learner = FALearner(MealyEncoder())
    learner.set_timeout(10000)
    import os.path
    maestro_aut = build_automaton_from_dot("MealyMachine", os.path.join("resources", "models", "bankcards", "MAESTRO.dot"))
    maestro_sut = MealyMachineSimulation(maestro_aut)
    mbt = MealyRWalkFromState(maestro_sut, 3, 0.2)
    (model, statistics) = learn_mbt(learner, mbt, 10000)
    print(model)
    print(statistics)

def sim_learn_mbt_yan_mealy():
    learner = FALearner(MealyEncoder())
    learner.set_timeout(10000)
    import os.path
    maestro_aut = build_automaton_from_dot("MealyMachine", os.path.join("resources", "models", "bankcards", "MAESTRO.dot"))
    maestro_sut = MealyMachineSimulation(maestro_aut)
    yan_cmd = os.path.join("resources", "binaries", "yannakakis.exe")
    mbt = YannakakisTestGenerator(maestro_sut, yan_cmd)
    (model, statistics) = learn_mbt(learner, mbt, 10000)
    print(model)
    print(statistics)

sim_learn_mbt_yan_mealy()
#scalable_learn_mbt_mealy()
#scalable_learn_mbt_iora()
