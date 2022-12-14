from typing import Tuple

from learn import Learner
import z3
import model.ra
import define.ra


class RALearner(Learner):
    def __init__(self, encoder, solver=None, verbose=False):
        super().__init__()
        if encoder is None:
            raise Exception("RAEncoder has to be supplied")
        if not solver:
            solver = z3.Solver()
        self.encoder = encoder
        self.solver = solver
        self.verbose = verbose
        self.num_reg = None

    def add(self, trace):
        self.encoder.add(trace)

    def set_num_reg(self, num):
        self.num_reg = num

    def model(self, min_locations=1, max_locations=15, min_registers=0, max_registers=3, ensure_min=True,
              old_definition:define.ra.RegisterMachine = None, old_model:model.ra.RegisterMachine = None) -> \
            Tuple[model.ra.RegisterMachine, define.ra.RegisterMachine]:
        if old_definition is not None:
            min_locations = len(old_definition.locations)
            min_registers = len(old_definition.registers) - 1

        (succ, ra_def, m) = self._learn_model(min_locations=min_locations,
                                        max_locations=max_locations, min_registers=min_registers,
                                              max_registers=max_registers, ensure_min=ensure_min)

        if succ:
            return ra_def.export(m), ra_def
        else:
            return None

    def _learn_model(self, min_locations, max_locations, min_registers, max_registers=3, ensure_min=True):
        """generates the definition and model for an ra whose traces include the traces added so far"""
        for num_locations in range(min_locations, max_locations + 1):
            # TODO: calculate max registers based on repeating values
            rng = range(min_registers, min(max_registers, num_locations) + 1) if self.num_reg is None else [self.num_reg]
            for num_registers in rng:
                ra, constraints = self.encoder.build(num_locations, num_registers)
                self.solver.add(constraints)
                if self.timeout is not None:
                    self.solver.set("timeout", self.timeout)
                self.solver.set(":smt.random_seed", 0) # this is a futile attempt of making Z3 deterministic
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
                    if result == z3.unknown and ensure_min:
                        print("Timeout at {0} locations and {1} registers".format(num_locations, num_registers))
                        return (False, True, None)

                    # TODO: process the unsat core?
                    pass

        return  (False, False, None)