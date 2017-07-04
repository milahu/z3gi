from typing import List, Tuple
from typing import cast

from model import Automaton
from learn import Learner
from test import TestTemplate

class Statistics():
    def __init__(self):
        self.num_tests = 0
        self.num_inputs = 0
        self.suite_size = 0

    def add_inputs(self, num):
        self.num_inputs += num

    def add_tests(self, num):
        self.num_tests += num

    def set_suite_size(self, num):
        self.suite_size = num

    def __str__(self):
        return "Total number tests used in learning: {0} \n" \
               "Total number inputs used in learning: {1} \n " \
               "Test suite size: {2}".format(self.num_tests,
                                             self.num_inputs,
                                             self.suite_size)


def learn(learner:Learner, test_type:type, traces: List[object]) -> Tuple[Automaton, Statistics]:
    statistics = Statistics()
    if len(traces) == 0:
        return (None, statistics)
    else:
        statistics.set_suite_size(len(traces))
        test = cast(TestTemplate, test_type(traces.pop(0)))
        definition = None
        learner.add(test.trace)
        statistics.add_tests(1)
        statistics.add_inputs(test.size())
        done = False
        model = None
        while not done:
            (model, definition) = learner.model(old_definition=definition)
            done = True
            for trace in traces:
                test = cast(TestTemplate, test_type(trace))
                ce = test.check(model)
                if ce is not None:
                    learner.add(ce)
                    statistics.add_tests(1)
                    statistics.add_inputs(test.size())
                    done = False
                    break
        return (model, statistics)