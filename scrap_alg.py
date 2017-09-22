import itertools

from encode.fa import MealyEncoder, DFAEncoder
from encode.ra import RAEncoder
from learn.algorithm import learn
from learn.algorithm import learn_mbt
from learn.fa import FALearner
from learn.ra import RALearner
from sut import SUTType
from sut.fifoset import FIFOSetClass
from sut.login import new_login_sut, LoginClass
from test import IORATest, MealyTest
from test.rwalk import IORARWalkFromState, MealyRWalkFromState, DFARWalkFromState, RARWalkFromState
from tests.iora_testscenario import *
from encode.iora import IORAEncoder

def scrap_learn_iora():
    learner = RALearner(IORAEncoder())
    test_type = IORATest
    exp = sut_m5
    (model, statistics) = learn(learner, test_type, exp.traces)
    print(model)
    print(statistics)

def scrap_learn_mbt_iora():
    learner = RALearner(IORAEncoder())
    learner.set_timeout(10000)
    sut = new_login_sut(1)
    mbt = IORARWalkFromState(sut, 5, 0.2)
    (model, statistics) = learn_mbt(learner, mbt, 10000)
    print(model)
    print(statistics)

def scrap_learn_mbt_mealy():
    learner = FALearner(MealyEncoder())
    learner.set_timeout(1000)
    login = LoginClass()
    sut = login.new_sut(SUTType.Mealy, 2)
    mbt = MealyRWalkFromState(sut, 5, 0.2)
    (model, statistics) = learn_mbt(learner, mbt, 10000)
    print(model)
    print(statistics)

def scrap_learn_mbt_mealy():
    learner = FALearner(DFAEncoder())
    learner.set_timeout(100000)
    login = LoginClass()
    sut = login.new_sut(SUTType.DFA, 2)
    mbt = DFARWalkFromState(sut, 5, 0.2)
    (model, statistics) = learn_mbt(learner, mbt, 10000)
    print(model)
    print(statistics)

def scrap_learn_mbt_ra():
    learner = RALearner(RAEncoder())
    learner.set_timeout(600000)
    login = FIFOSetClass()
    sut = login.new_sut(SUTType.RA, 1)
    mbt = RARWalkFromState(sut, 5, 0.2)
    (model, statistics) = learn_mbt(learner, mbt, 10000)
    print(model)
    print(statistics)

#scrap_learn_mbt_mealy()
#scrap_learn_mbt_mealy()
scrap_learn_mbt_iora()
