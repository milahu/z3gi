import unittest

from tests.ra_testscenario import *
from z3gi.learn.ra import RALearner
from z3gi.define.ra import RegisterAutomaton

class RaTest(unittest.TestCase):

    def setUp(self):
        self.ralearner = RALearner(labels, verbose=True)

    def test_sut1(self):
        self.check_scenario(sut_m1)
        # pass

    #def test_sut2(self):
    #    pass
    #    # self.check_scenario(sut_m2)
    #
    #def test_sut3(self):
    #    pass
    ##    self.check_scenario(sut_m3)

    def check_scenario(self, test_scenario : RaTestScenario):
        ra = self.learn_model(test_scenario)
        self.assertIsNotNone(ra, "Register Automaton could not be inferred")
        self.assertEqual(len(ra.locations), test_scenario.nr_locations,
                         "Wrong number of locations")
        self.assertEqual(len(ra.locations), test_scenario.nr_locations,
                         "Wrong number of registers")

    def learn_model(self, test_scenario : RaTestScenario) -> RegisterAutomaton:
        for trace in test_scenario.traces:
            self.ralearner.add(trace)
        return self.ralearner.model()



