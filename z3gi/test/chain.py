from typing import List

from model import Automaton
from test import TestGenerator

"""Used to chain multiple test generators"""
class TestGeneratorChain(TestGenerator):

    def __init__(self, test_gen:List[TestGenerator]):
        self._generators = test_gen
        self._test_iter = None

    def initialize(self, model: Automaton):
        for test_gen in self._generators:
            test_gen.initialize(model)
        self._test_iter = self.gen_test_iter(model)

    def gen_test(self, model: Automaton):
        try:
            return next(self._test_iter)
        except StopIteration:
            return None

    def gen_test_iter(self, model: Automaton):
        for test_gen in self._generators:
            next_test = test_gen.gen_test(model)
            while next_test is not None:
                yield next_test
                next_test = test_gen.gen_test(model)

    def terminate(self):
        for test_gen in self._generators:
            test_gen.terminate()