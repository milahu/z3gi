import unittest
import sys
import os.path
from parse.importer import build_automaton_from_dot

from model.fa import MealyMachine
from sut.simulation import MealyMachineSimulation


class MealyImporterTest(unittest.TestCase):

    def check_aut(self, aut:MealyMachine, exp_num_states=None, exp_num_trans=None):
        self.assertIsNotNone(aut, "Machine is None (either parsing failed or couldn't find machine)")
        if exp_num_states is not None:
            self.assertEqual(len(aut.states()), exp_num_states, "Number of states not equal to expected")
        if exp_num_trans is not None:
            self.assertEqual(len(aut.transitions()), exp_num_trans, "Number of transitions not equal to expected")

    def test_banking(self):
        maestro_model_file = os.path.join("..","resources","models","bankcards","MAESTRO.dot")
        mealy = build_automaton_from_dot("MealyMachine", maestro_model_file)
        self.check_aut(mealy, exp_num_states=6)
        sim = MealyMachineSimulation(mealy)
        self.assertEqual(sim.run(["getValidData","selectApplication"]).trace(),
                         [('getValidData', '6A88'), ('selectApplication', '9000')])



