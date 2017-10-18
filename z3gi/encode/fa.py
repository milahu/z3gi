import itertools

import z3

from define.fa import DFA, MealyMachine, Mapper
from encode import Encoder
from utils import Tree



class DFAEncoder(Encoder):
    def __init__(self):
        self.tree = Tree(itertools.count(0))
        self.cache = {}
        self.labels = set()

    def add(self, trace):
        seq, accept = trace
        node = self.tree[seq]
        self.cache[node] = accept
        self.labels.update(seq)

    def build(self, num_states):
        dfa = DFA(list(self.labels), num_states)
        mapper = Mapper(dfa)
        constraints = self.axioms(dfa, mapper)
        constraints += self.node_constraints(dfa, mapper)
        constraints += self.transition_constraints(dfa, mapper)
        return dfa, constraints

    def axioms(self, dfa: DFA, mapper: Mapper):
        return [
            z3.And([z3.And([z3.Or([dfa.transition(state, label) == to_state
                                   for to_state in dfa.states]) for state in dfa.states])
                    for label in dfa.labels.values()]),
            z3.Distinct(list(dfa.labels.values())),
            z3.Distinct(list(dfa.states)),
            z3.Distinct([mapper.element(node.id) for node in self.cache])
        ]

    def node_constraints(self, dfa, mapper):
        constraints = []
        for node in self.cache:
            accept = self.cache[node]
            n = mapper.element(node.id)
            constraints.append(dfa.output(mapper.map(n)) == accept)
        return constraints

    def transition_constraints(self, dfa, mapper):
        constraints = [dfa.start == mapper.map(mapper.start)]
        for node, label, child in self.tree.transitions():
            n = mapper.element(node.id)
            l = dfa.labels[label]
            c = mapper.element(child.id)
            constraints.append(dfa.transition(mapper.map(n), l) == mapper.map(c))
        return constraints

class MealyEncoder(Encoder):
    def __init__(self):
        self.tree = Tree(itertools.count(0))
        self.cache = {}
        self.input_labels = set()
        self.output_labels = set()


    def add(self, trace):
        input_sequence = [input for (input, _) in trace]
        output_sequence = [output for (_, output) in trace]
        for i in range(len(input_sequence)):
            node = self.tree[input_sequence[:i+1]]
            self.cache[node] = output_sequence[i]
        self.input_labels.update(input_sequence)
        self.output_labels.update(output_sequence)


    def build(self, num_states) -> (MealyMachine, z3.ExprRef):
        mm = MealyMachine(list(self.input_labels), list(self.output_labels), num_states)
        mapper = Mapper(mm)
        constraints = self.axioms(mm, mapper)
        constraints += self.node_constraints(mm, mapper)
        constraints += self.transition_constraints(mm, mapper)
        return mm, constraints

    def axioms(self, mm: MealyMachine, mapper: Mapper):
        return [
            z3.And([z3.And([z3.Or([mm.transition(state, input) == to_state
                                     for to_state in mm.states]) for state in mm.states])
                  for input in mm.inputs.values()]),
            z3.Distinct(list(mm.inputs.values())),
            z3.Distinct(list(mm.outputs.values())),
            z3.Distinct(list(mm.states)),
            z3.Distinct([mapper.element(node.id) for node in self.cache])
        ]
        #return []

    def node_constraints(self, mm, mapper):
        constraints = []
        for node in self.cache:
            parent = node.parent
            input = None
            for label in parent.children:
                if parent.children[label] is node:
                    input = label
                    break
            output = self.cache[node]
            n = mapper.element(parent.id)
            i = mm.inputs[input]
            o = mm.outputs[output]
            constraints.append(mm.output(mapper.map(n), i) == o)
        return constraints

    def transition_constraints(self, mm, mapper):
        constraints = [mm.start == mapper.map(mapper.start)]
        for node, input, child in self.tree.transitions():
            n = mapper.element(node.id)
            i = mm.inputs[input]
            c = mapper.element(child.id)
            constraints.append(mm.transition(mapper.map(n), i) == mapper.map(c))
        return constraints