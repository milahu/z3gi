from typing import List, Tuple
from typing import cast

from model import Automaton
from learn import Learner
from test import TestTemplate, TestGenerator
import time

class Statistics():
    def __init__(self):
        self.num_tests = 0
        self.num_inputs = 0
        self.suite_size = 0
        self.learning_times = []

    def add_inputs(self, num):
        self.num_inputs += num

    def add_tests(self, num):
        self.num_tests += num

    def set_suite_size(self, num):
        self.suite_size = num

    def add_learning_time(self, time):
        self.learning_times.append(time)

    def __str__(self):        return "Total number tests used in learning: {0} \n" \
               "Total number inputs used in learning: {1} \n " \
               "Test suite size: {2} \n " \
               "Learning time for each model: {3} \n " \
               "Total learning time: {4} ".format(self.num_tests,
                                                  self.num_inputs,
                                                  self.suite_size,
                                                  self.learning_times,
                                                  sum(self.learning_times))


def learn(learner:Learner, test_type:type, traces: List[object]) -> Tuple[Automaton, Statistics]:
    """ takes learner and a list of traces and generates a model"""
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
        learn_traces = [test.trace]
        while not done:
            start_time = int(time.time() * 1000)
            (model, definition) = learner.model(old_definition=definition)
            end_time = int(time.time() * 1000)
            statistics.add_learning_time(end_time-start_time)
            done = True
            for trace in traces:
                test = cast(TestTemplate, test_type(trace))
                ce = test.check(model)
                if ce is not None:
                    if ce not in learn_traces:
                        learn_traces.append(ce)
                    else:
                        raise Exception("The CE {0} has already been processed yet it "
                                        "is still a CE. \n CEs: {1} \n Model: {2}".format(ce, learn_traces, model))
                    learner.add(ce)
                    statistics.add_tests(1)
                    statistics.add_inputs(test.size())
                    done = False
                    break
        return (model, statistics)

def learn_mbt(learner:Learner, test_generator:TestGenerator) -> Tuple[Automaton, Statistics]:
    """ takes learner and a test generator, and generates a model"""
    next_test = test_generator.gen_test(None)
    statistics = Statistics()
    if next_test is None:
        return (None, statistics)
    else:
        definition = None
        learner.add(next_test.trace())
        statistics.add_tests(1)
        statistics.add_inputs(next_test.size())
        done = False
        learner_tests = [next_test]
        generated_tests = [next_test]
        while not done:
            start_time = int(time.time() * 1000)
            (model, definition) = learner.model(old_definition=definition)
            end_time = int(time.time() * 1000)
            statistics.add_learning_time(end_time - start_time)
            done = True
            for next_test in generated_tests:
                ce = next_test.check(model)
                if ce is not None:
                    learner_tests.append(ce)
                    learner.add(ce)
                    statistics.add_tests(1)
                    statistics.add_inputs(next_test.size())
                    done = False
                    break
            if not done:
                continue
            for next_test in test_generator.gen_test_iter(model):
                generated_tests.append(next_test)
                ce = next_test.check(model)
                if ce is not None:
                    learner_tests.append(ce)
                    learner.add(ce)
                    statistics.add_tests(1)
                    statistics.add_inputs(next_test.size())
                    done = False
                    break
        statistics.set_suite_size(len(generated_tests))
        return (model, statistics)
