import z3

from z3gi.define import Automaton

class RegisterAutomaton(Automaton):

    def __init__(self, labels, num_locations, num_registers):
        self.Label, self.labels = enum('Label', labels)
        self.Location, self.locations = enum('Location', ['location{0}'.format(i) for i in range(num_locations)])
        self.Register, self.registers = enum('Register', ['register{0}'.format(i) for i in range(num_registers)] + ['fresh'])
        self.start = self.locations[0]
        self.transition = z3.Function('transition', self.Location, self.Label, self.Register, self.Location)
        self.output = z3.Function('output', self.Location, z3.BoolSort())
        self.used = z3.Function('used', self.Location, self.Register, z3.BoolSort())
        self.guard = z3.Function('guard', self.Location, self.Label, self.Register)
        self.update = z3.Function('update', self.Location, self.Label, self.Register)

    def export(self):
        pass


def enum(name, elements):
    d = z3.Datatype(name)
    for element in elements:
        d.declare(element)
    d = d.create()
    return d, [d.__getattribute__(element) for element in elements]
