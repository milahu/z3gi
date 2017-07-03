import itertools

from define.fa import DFA, MealyMachine, Mapper
from encode import Encoder
from utils import Tree
from model.fa import MealyMachine
import z3


class DFAEncoder(Encoder):
    def __init__(self, labels):
        self.tree = Tree(itertools.count(0))
        self.cache = {}
        self.labels = set()

    def add(self, trace):
        seq, accept = trace
        node = self.tree[seq]
        self.cache[node] = accept
        self.labels.update(seq)

    def build(self, num_states):
        dfa = DFA(self.labels, num_states)
        mapper = Mapper(dfa)
        constraints = self.axioms(dfa, mapper)
        constraints += self.node_constraints(dfa, mapper)
        constraints += self.transition_constraints(dfa, mapper)
        return dfa, constraints

    def axioms(self, dfa: DFA, mapper: Mapper):
        return []

    def node_constraints(self, dfa, mapper):
        constraints = []
        for node, accept in self.cache:
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
    def __init__(self, input_labels, output_labels):
        self.tree = Tree(itertools.count(0))
        self.cache = {}
        self.input_labels = set()
        self.output_labels = set()


    def add(self, trace):
        _ = self.tree[trace]
        self.input_labels.update([input_label for input_label in [i for (i, _) in trace]])
        self.output_labels.update([output_label for output_label in [o for (_, o) in trace]])


    def build(self, num_states) -> (MealyMachine, z3.ExprRef):
        return None

