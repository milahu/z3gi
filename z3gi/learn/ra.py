import z3

from z3gi.define.ra import RegisterAutomaton
from z3gi.encode.ra import RAEncoder
from z3gi.learn import Learner


class RALearner(Learner):
    def __init__(self, labels, encoder=None, solver=None):
        if not encoder:
            encoder = RAEncoder()
        if not solver:
            solver = z3.Solver()
        self.labels = labels
        self.encoder = encoder
        self.solver = solver
        self.previous_model = None
        self.num_locations = None
        self.num_registers = None

    def add(self, trace):
        self.encoder.add(trace)

    def model(self, min_locations=1, max_locations=20):
        if self.num_locations is None:
            self.num_locations = min_locations
        if self.num_registers is None:
            self.num_registers = 0

        num_values = len(self.encoder.values)
        for num_locations in range(max(self.num_locations, min_locations), max_locations+1):
            for num_registers in range(self.num_registers, min(num_values, num_locations)):
                ra = RegisterAutomaton(labels=self.labels, num_locations=num_locations, num_registers=num_registers)
                constraints = self.encoder.build(ra)
                self.solver.add(constraints)
                if self.solver.check() == z3.sat:
                    model = self.solver.model()
                    # TODO: process model here
                    self.num_locations = num_locations
                    self.num_registers = num_registers
                    self.previous_model = model
                    return model
                else:
                    # TODO: process the unsat core?
                    pass