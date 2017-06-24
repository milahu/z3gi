import unittest

from tests.ra_testscenario import RaTestScenario
from z3gi.learn.ra import RALearner

class RaTest(unittest.TestCase):
    def __init__(self):
        super.__init__()

    def setUp(self):
        self.ralearner = RALearner()

    #def check_for_model(self, ):

    def learn_model(self, sut : RaTestScenario):
        for trace in sut.traces:
            self.ralearner.add(trace)
        return self.ralearner.model()



