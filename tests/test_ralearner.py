import unittest

from tests.ra_testscenario import *
from z3gi.learn.ra import RALearner
from z3gi.define.ra import RegisterAutomaton
import z3

class RaTest(unittest.TestCase):

    def setUp(self):
        self.ralearner = RALearner(labels, verbose=True)


    def test_sut1(self):
        self.check_scenario(sut_m1)
        pass

    def test_sut2(self):
        self.check_scenario(sut_m2)

    def test_sut3(self):
        self.check_scenario(sut_m3)

    def check_scenario(self, test_scenario : RaTestScenario):
        print("Scenario " + test_scenario.description)
        #result = self.learn_model(test_scenario)
        (succ, ra, model) = self.learn_model(test_scenario)
        self.assertTrue(succ, msg="Register Automaton could not be inferred")
        self.assertEqual(len(ra.locations), test_scenario.nr_locations,
                         "Wrong number of locations." )
        self.assertEqual(len(ra.locations), test_scenario.nr_locations,
                         "Wrong number of registers.")
    
    def learn_model(self, test_scenario : RaTestScenario):
        for trace in test_scenario.traces:
            self.ralearner.add(trace)
        #ra_def = None
        min_locations = 0
        max_locations = test_scenario.nr_locations + 1
        num_regs = 0
        #(_, ra_def, _) = self.ralearner._learn_model(2, 2, 1)
        result = self.ralearner._learn_model(min_locations, max_locations, num_regs)  #
        return result



