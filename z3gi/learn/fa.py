from typing import Tuple

import z3

from encode.ra import RAEncoder
from learn import Learner
import model.fa

import z3

from encode.fa import DFAEncoder, MealyEncoder
from learn import Learner
from model import Automaton
import define.fa

class FALearner(Learner):
    def __init__(self, encoder, solver=None, verbose=False):
        if not solver:
            solver = z3.Solver()
        self.solver = solver
        self.encoder = encoder
        self.verbose = verbose

    def add(self, trace):
        self.encoder.add(trace)

    def model(self, min_states=1, max_states=20, old_definition:define.fa.FSM=None) -> Tuple[Automaton, define.fa.FSM]:
        if old_definition is not None:
            min_states = len(old_definition.states)
        (succ, fa, m) = self._learn_model(min_states=min_states,
                                        max_states=max_states)
        if succ:
            return (fa.export(m), fa)
        return None

    def _learn_model(self, min_states=1, max_states=20):
        """generates the definition and model for an fa whose traces include the traces added so far"""
        for num_states in range(min_states, max_states + 1):
            fa, constraints = self.encoder.build(num_states)
            self.solver.add(constraints)
            result = self.solver.check()
            if self.verbose:
                print("Learning with {0} states. Result: {1}"
                  .format(num_states, result))
            if result == z3.sat:
                model = self.solver.model()
                self.solver.reset()
                return (True, fa, model)
            else:
                self.solver.reset()
                # TODO: process the unsat core?
                pass
        return (False, None, None)