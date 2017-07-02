import itertools

from encode import Encoder
from utils import Tree
from model.fa import MealyMachine
import z3


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

