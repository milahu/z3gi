import itertools

from learn.algorithm import learn
from learn.algorithm import learn_mbt
from learn.ra import RALearner
from sut.login import new_login_sut
from test import IORATest
from test.rwalk import IORARWalkFromState
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
    sut = new_login_sut(1)
    mbt = IORARWalkFromState(sut, 10)
    (model, statistics) = learn_mbt(learner, mbt, 1000)
    print(model)
    print(statistics)

scrap_learn_mbt_iora()