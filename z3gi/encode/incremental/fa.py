import itertools

from z3 import z3

from define import int_enum
from define.fa import MealyMachine
from encode import IncrementalEncoder
from utils import Tree


# dirty incremental mealy tree encoders, just for experimentation
# result: it using incremental solving yields no benefit
class MealyTreeIEncoder(IncrementalEncoder):
    def __init__(self):
        self.tree = Tree(itertools.count(0))
        self.cache = {}
        self.inputs = dict()
        self.outputs = dict()
        self.State = z3.DeclareSort("State")
        self.Element = z3.DeclareSort('Element')
        self.start_node = self.element(0)
        self.map = z3.Function('map', self.Element, self.State)
        self.Input = z3.DeclareSort("Input")
        self.Output = z3.DeclareSort("Output")
        self.start = z3.Const("start", self.State)
        self.transition = z3.Function('transition', self.State, self.Input, self.State)
        self.output = z3.Function('output', self.State, self.Input, self.Output)

    def trace(self, trace):
        self._update_labels(trace)
        first = len(self.cache) == 0
        inputs = []
        new_nodes = []
        for i,o in trace:
            inputs.append(i)
            node = self.tree[inputs]
            if node not in self.cache:
                new_nodes.append(node)
                self.cache[node] = o

        trace_constraints = self._trace_constraint(new_nodes)
        if first:
            trace_constraints = z3.And(trace_constraints, self.map(self.start_node) == self.start)
        return z3.And(trace_constraints)

    def _trace_constraint(self, new_nodes):
        transition_constraints = []
        node_constraints = []
        for node in new_nodes:
            parent = node.parent
            input = None
            for label in parent.children:
                if parent.children[label] is node:
                    input = label
                    break
            output = self.cache[node]
            n = self.element(parent.id)
            i = self.inputs[input]
            o = self.outputs[output]
            node_constraints.append(self.output(self.map(n), i) == o)
            c = self.element(node.id)
            transition_constraints.append(self.transition(self.map(n), i) == self.map(c))
        return z3.And(node_constraints + transition_constraints)

    def element(self, name):
        return z3.Const("n"+str(name), self.Element)

    def _update_labels(self, trace):
        input_sequence = [input for (input, _) in trace]
        output_sequence = [output for (_, output) in trace]

        for input in input_sequence:
            if input not in self.inputs:
                self.inputs[input] = z3.Const(input, self.Input)

        for output in set(output_sequence):
            if output not in self.outputs:
                self.outputs[output] = z3.Const(output, self.Output)

    def automaton(self, num_states):
        states = [self.start] + [z3.Const("q"+str(i), self.State) for i in range(1,num_states)]
        cst = [z3.And([
            z3.And([
                z3.Or([
                    self.transition(state, inp) == to_state for to_state in states])
                for inp in iter(self.inputs.values())]) for state in states])]
        cst.extend(
            [ z3.Distinct(states), z3.Distinct(list(self.inputs.values())), z3.Distinct(list(self.outputs.values()))]
        )

        mm_def = MealyMachine(list(self.inputs.keys()), list(self.outputs.keys()), num_states,
                              state_enum=int_enum, label_enum=int_enum)
        mm_def.transition = self.transition
        mm_def.output = self.output
        mm_def.inputs = self.inputs
        mm_def.outputs = self.outputs
        mm_def.states = states
        mm_def.start = self.start
        return (z3.And(cst), mm_def)


class MealyIEncoder(IncrementalEncoder):
    def __init__(self):
        self.inputs = dict()
        self.outputs = dict()
        self.State = z3.DeclareSort("State")
        self.Input = z3.DeclareSort("Input")
        self.Output = z3.DeclareSort("Output")
        self.start = z3.Const("start", self.State)
        self.transition = z3.Function('transition', self.State, self.Input, self.State)
        self.output = z3.Function('output', self.State, self.Input, self.Output)

    def trace(self, trace):
        self._update_labels(trace)
        trace_const = self._trace_constraint(trace)
        return trace_const

    def _trace_constraint(self, trace):
        crt_state = self.start
        trace_constraints = []
        for (input, output) in trace:
            z3_inp, z3_out = self.inputs[input], self.outputs[output]
            trace_constraints.append(self.output(crt_state, z3_inp) == z3_out)
            crt_state = self.transition(crt_state, z3_inp)

        return z3.And(trace_constraints)

    def _update_labels(self, trace):
        input_sequence = [input for (input, _) in trace]
        output_sequence = [output for (_, output) in trace]

        for input in input_sequence:
            if input not in self.inputs:
                self.inputs[input] = z3.Const(input, self.Input)

        for output in set(output_sequence):
            if output not in self.outputs:
                self.outputs[output] = z3.Const(output, self.Output)

    def automaton(self, num_states):
        states = [self.start] + [z3.Const("q"+str(i), self.State) for i in range(1,num_states)]
        cst = [z3.And([
            z3.And([
                z3.Or([
                    self.transition(state, inp) == to_state for to_state in states])
                for inp in iter(self.inputs.values())]) for state in states])]
        cst.extend(
            [ z3.Distinct(states), z3.Distinct(list(self.inputs.values())), z3.Distinct(list(self.outputs.values()))]
        )

        mm_def = MealyMachine(list(self.inputs.keys()), list(self.outputs.keys()), num_states,
                              state_enum=int_enum, label_enum=int_enum)
        mm_def.transition = self.transition
        mm_def.output = self.output
        mm_def.inputs = self.inputs
        mm_def.outputs = self.outputs
        mm_def.states = states
        mm_def.start = self.start
        return (z3.And(cst), mm_def)
