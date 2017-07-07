from typing import Tuple

import z3

from learn import Learner
import model.ra
import define.ra


class RALearner(Learner):
    def __init__(self, encoder, solver=None, verbose=False):
        if encoder is None:
            raise Exception("RAEncoder has to be supplied")
        if not solver:
            solver = z3.Solver()
        self.encoder = encoder
        self.solver = solver
        self.verbose = verbose

    def add(self, trace):
        self.encoder.add(trace)

    def model(self, min_locations=1, max_locations=20, min_registers=0, max_registers=3,
              old_definition:define.ra.RegisterMachine = None, old_model:model.ra.RegisterMachine = None) -> \
            Tuple[model.ra.RegisterMachine, define.ra.RegisterMachine]:
        if old_definition is not None:
            min_locations = len(old_definition.locations)
            min_registers = len(old_definition.registers) - 1

        (succ, ra_def, m) = self._learn_model(min_locations=min_locations,
                                        max_locations=max_locations, min_registers=min_registers,
                                              max_registers=max_registers)
        if succ:
            return (ra_def.export(m), ra_def)
        return None

    def _learn_model(self, min_locations=1, max_locations=20, min_registers=0, max_registers=10):
        """generates the definition and model for an ra whose traces include the traces added so far"""
        for num_locations in range(min_locations, max_locations + 1):
            # TODO: calculate max registers based on repeating values
            for num_registers in range(min_registers, min(max_registers, num_locations) + 1):
                ra, constraints = self.encoder.build(num_locations, num_registers)
                self.solver.add(constraints)
                print(num_locations, num_registers)
                result = self.solver.check()
                if self.verbose:
                    print("Learning with {0} locations and {1} registers. Result: {2}"
                      .format(num_locations, num_registers, result))
                if result == z3.sat:
                    model = self.solver.model()
                    self.solver.reset()
                    return (True, ra, model)
                else:
                    self.solver.reset()
                    # TODO: process the unsat core?
                    pass

        return  (False, None, None)