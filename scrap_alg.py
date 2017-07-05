import itertools

from learn.algorithm import learn
from learn.ra import RALearner
from test import IORATest
from tests.iora_testscenario import *
from encode.iora import IORAEncoder

learner = RALearner(IORAEncoder())
test_type = IORATest
exp = sut_m5
(model, statistics) = learn(learner, test_type, exp.traces)
print(model)
print(statistics)
