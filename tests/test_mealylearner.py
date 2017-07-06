import unittest

from encode.fa import MealyEncoder
from tests.mealy_testscenario import *
from z3gi.learn.fa import FALearner

num_exp = 1


class MealyLearnerTest(unittest.TestCase):
    def setUp(self):
        pass

    def test_sut1(self):
        self.check_scenario(sut_m1)

    def check_scenario(self, test_scenario):
        print("Scenario " + test_scenario.description)

        for i in range(0, num_exp):
            (succ, fa, model) = self.learn_model(test_scenario)

            self.assertTrue(succ, msg="Automaton could not be inferred")
            self.assertEqual(len(fa.states), test_scenario.nr_states,
                             "Wrong number of states.")
            self.assertEqual(len(fa.states), test_scenario.nr_states,
                             "Wrong number of registers.")
            exported = fa.export(model)
            print("Learned model:  \n", exported)
            self.assertEqual(len(exported.states()), test_scenario.nr_states,
                             "Wrong number of states in exported model. ")
            self.check_against_obs(exported, test_scenario)

    def check_against_obs(self, learned_fa, test_scenario):
        """Checks if the learned RA corresponds to the scenario observations"""
        for trace, acc in test_scenario.traces:
            self.assertEqual(learned_fa.accepts(trace), acc,
                             "Register automaton output doesn't correspond to observation {0}".format(str(trace)))

    def learn_model(self, test_scenario):
        # inputs = set()
        # outputs = set()
        # for trace in test_scenario.traces:
        #     inputs.update([i for (i, _) in trace])
        #     outputs.update([o for (_, o) in trace])
        learner = FALearner(encoder=MealyEncoder(),  verbose=True)
        for trace in test_scenario.traces:
            learner.add(trace)

        min_states = test_scenario.nr_states - 1
        max_states = test_scenario.nr_states + 1

        result = learner._learn_model(min_states, max_states)  #
        return result