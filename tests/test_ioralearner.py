import unittest

from tests.iora_testscenario import *
from z3gi.learn.ra import RALearner
from encode.iora import IORAEncoder


class RaTest(unittest.TestCase):
    def setUp(self):
        self.ralearner = RALearner(IORAEncoder(), verbose=True)

    def test_sut1(self):
        self.check_scenario(sut_m1)

    def test_sut2(self):
        self.check_scenario(sut_m2)

    def test_sut3(self):
        self.check_scenario(sut_m3)

    def test_sut4(self):
        self.check_scenario(sut_m4)

    def check_scenario(self, test_scenario: RaTestScenario):
        print("Scenario " + test_scenario.description)
        result = self.learn_model(test_scenario)
        self.assertTrue(result, msg="Register Automaton could not be inferred")
        (iora, iora_def) = result
        self.assertEqual(len(iora_def.locations), test_scenario.nr_locations, "Wrong number of locations.")

    def learn_model(self, test_scenario: RaTestScenario):
        for trace in test_scenario.traces:
            self.ralearner.add(trace)
        min_locations = 1
        max_locations = test_scenario.nr_locations + 1
        num_regs = 0
        result = self.ralearner.model(min_locations, max_locations, num_regs)  #
        return result



