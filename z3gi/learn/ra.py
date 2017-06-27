import z3

from define.ra import RegisterAutomaton, IORegisterAutomaton
from encode.ra import RAEncoder
from learn import Learner
import model.ra


class RALearner(Learner):
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
        self.previous_model = None
        self.num_locations = None
        self.num_registers = None
        self.verbose = verbose
        self.io = io

    def add(self, trace):
        self.encoder.add(trace)

    def model(self, min_locations=1, max_locations=20, num_registers=0) -> model.ra.RegisterAutomaton:
        (succ, ra_def, m) = self._learn_model(min_locations=min_locations,
                                        max_locations=max_locations, num_registers=num_registers)
        if succ:
            return ra_def.export(m)
        return None

    def _learn_model(self, min_locations, max_locations, num_registers) -> \
            (bool, RegisterAutomaton, z3.ModelRef):
        """generates the definition and model for an ra whose traces include the traces added so far"""
        if self.num_locations is None:
            self.num_locations = min_locations
        if self.num_registers is None:
            self.num_registers = num_registers
        num_values = len(self.encoder.values)
        for num_locations in range(max(self.num_locations, min_locations), max_locations + 1):
            for num_registers in range(self.num_registers, max(self.num_registers, min(num_values, num_locations))):
                if self.io:
                    ra = IORegisterAutomaton(inputs=self.labels, outputs=self.outputs, num_locations=num_locations, num_registers=num_registers)
                else:
                    ra = RegisterAutomaton(labels=self.labels, num_locations=num_locations, num_registers=num_registers)
                constraints = self.encoder.build(ra)
                self.solver.add(constraints)
                result = self.solver.check()
                if self.verbose:
                    print("Learning with {0} locations and {1} registers. Result: {2}"
                          .format(num_locations, num_registers, result))
                if result == z3.sat:
                    model = self.solver.model()
                    self.num_locations = num_locations
                    self.num_registers = num_registers
                    self.previous_model = model
                    self.solver.reset()
                    return (True, ra, model)
                else:
                    self.solver.reset()
                    # TODO: process the unsat core?
                    pass

        return  (False, None, None)