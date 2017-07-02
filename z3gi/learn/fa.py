import z3

from encode.ra import RAEncoder
from learn import Learner
import model.fa


class MealyLearner(Learner):
    def __init__(self, labels, io=False, outputs=None, encoder=None, solver=None, verbose=False):
        if not encoder:
            encoder = RAEncoder()
        if not solver:
            solver = z3.Solver()
        if outputs:
            self.outputs = outputs
        self.labels = labels
        self.encoder = encoder
        self.solver = solver
        self.verbose = verbose
        self.io = io

    def add(self, trace):
        self.encoder.add(trace)

    def model(self, min_states=1, max_states=20) -> model.fa.MealyMachine:
        (succ, ra_def, m) = self._learn_model(min_states=min_states,
                                        max_states=max_states)
        if succ:
            return ra_def.export(m)
        return None

    def _learn_model(self, min_states=1, max_states=20):
        """generates the definition and model for an ra whose traces include the traces added so far"""
        num_values = len(self.encoder.values)
        for num_locations in range(min_states, max_states + 1):
            ra, constraints = self.encoder.build(num_locations)
            self.solver.add(constraints)
            result = self.solver.check()
            if self.verbose:
                print("Learning with {0} states. Result: {1}"
                  .format(num_locations, result))
            if result == z3.sat:
                model = self.solver.model()
                self.solver.reset()
                return (True, ra, model)
            else:
                self.solver.reset()
                # TODO: process the unsat core?
                pass
        return (False, None, None)