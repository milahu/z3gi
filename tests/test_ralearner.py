import unittest

from encode.ra import RAEncoder
from tests.ra_testscenario import *
from z3gi.learn.ra import RALearner
from z3gi.define.ra import RegisterAutomaton
import model.ra
import z3

num_exp = 1

class RaLearnerTest(unittest.TestCase):

    def setUp(self):
        pass


    def test_sut1(self):
        self.check_scenario(sut_m1)

    def test_sut2(self):
        self.check_scenario(sut_m2)

    def test_sut3(self):
        self.check_scenario(sut_m3)

    def test_sut4(self):
        self.check_scenario(sut_m4)

    def test_sut5(self):
        self.check_scenario(sut_m5)

    def check_scenario(self, test_scenario : RaTestScenario):
        print("Scenario " + test_scenario.description)

        for i in range(0,num_exp):
            (succ, ra, model) = self.learn_model(test_scenario)

            self.assertTrue(succ, msg="Register Automaton could not be inferred")
            self.assertEqual(len(ra.locations), test_scenario.nr_locations,
                             "Wrong number of locations." )
            self.assertEqual(len(ra.locations), test_scenario.nr_locations,
                             "Wrong number of registers.")
            exported = ra.export(model)
            print("Learned model:  \n",exported)
            self.assertEqual(len(exported.states()), test_scenario.nr_locations,
                              "Wrong number of locations in exported model. ")
            self.assertEqual(len(exported.registers()), test_scenario.nr_registers,
                              "Wrong number of registers in exported model. ")
            self.check_ra_against_obs(exported, test_scenario)


    def check_ra_against_obs(self, learned_ra: model.ra.RegisterAutomaton, test_scenario : RaTestScenario):
        """Checks if the learned RA corresponds to the scenario observations"""
        for trace, acc in test_scenario.traces:
            self.assertEqual(learned_ra.accepts(trace), acc,
                             "Register automaton output doesn't correspond to observation {0}".format(str(trace)))
    
    def learn_model(self, test_scenario : RaTestScenario) -> \
            (bool, RegisterAutomaton, z3.ModelRef):
        ralearner = RALearner(RAEncoder())
        for trace in test_scenario.traces:
            ralearner.add(trace)

        min_locations = test_scenario.nr_locations - 1
        max_locations = test_scenario.nr_locations + 1

        result = ralearner._learn_model(min_locations, max_locations, test_scenario.nr_registers + 1)  #
        return result