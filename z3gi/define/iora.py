# TODO make standalone
from define import Automaton

class IORegisterAutomaton(Automaton):

    def __init__(self, inputs, outputs, num_locations, num_registers):
        super().__init__(inputs + outputs, num_locations + 1, num_registers)
        del self.output
        self.sink = self.locations[-1]
        self.statetype = z3.Function('statetype', self.Location, z3.BoolSort())

    def export(self, model):
        raise NotImplementedError()
