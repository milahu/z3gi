import copy
from typing import List, Tuple, Union,cast

from model import Automaton
from learn import Learner
from model.ra import Action
from sut import StatsTracker, SUT
from sut.scalable import ActionSignature
from test import TestGenerator, Test
import time

__all__ = [
    "learn",
    "learn_mbt"
    ]


class Statistics():
    """We only refe"""
    def __init__(self):
        self.learning_times = []
        self.model_stats = None
        self.resets = 0
        self.inputs = 0

    def add_learning_time(self, time):
        self.learning_times.append(time)

    def set_num_resets(self, test_num):
        self.resets = test_num

    def set_num_inputs(self, inp_num):
        self.inputs = inp_num

    def __str__(self):        return \
        "Tests until last hyp: {} \n" \
        "Inputs until last hyp: {} \n " \
        "Hypotheses used in learning: {} \n " \
        "Learning time for each model: {} \n " \
        "Total learning time: {} ".format(        self.resets,
                                                  self.inputs,
                                                   len(self.learning_times),
                                                  self.learning_times,
                                                   sum(self.learning_times))


def learn(learner:Learner, test_type:type, traces: List[object]) -> Tuple[Automaton, Statistics]:
    """ takes learner and a list of traces and generates a model"""
    statistics = Statistics()
    if len(traces) == 0:
        return (None, statistics)
    else:
        statistics.set_suite_size(len(traces))
        test = cast(Test, test_type(traces.pop(0)))
        definition = None
        learner.add(test.tr)
        statistics.add_learner_test(test)
        done = False
        model = None
        learn_traces = [test.tr]
        while not done:
            start_time = int(time.time() * 1000)
            (model, definition) = learner.model(old_definition=definition)
            end_time = int(time.time() * 1000)
            statistics.add_learning_time(end_time-start_time)
            done = True
            for trace in traces:
                test = cast(Test, test_type(trace))
                ce = test.check(model)
                if ce is not None:
                    if ce not in learn_traces:
                        learn_traces.append(ce)
                    else:
                        raise Exception("The CE {0} has already been processed yet it "
                                        "is still a CE. \n CEs: {1} \n Model: {2}".format(ce, learn_traces, model))
                    learner.add(ce)
                    statistics.add_learner_test(test)
                    done = False
                    break
        statistics.set_suite_size(len(traces))
        return (model, statistics)

def learn_mbt(sut:SUT, learner:Learner, test_generator:TestGenerator, max_tests:int, stats_tracker:StatsTracker=None) -> Tuple[Union[Automaton, None], Statistics]:
    """ takes learner, a test generator, and bound on the number of tests and generates a model"""
    next_test = gen_blind_test(sut)
    statistics = Statistics()
    if next_test is None:
        return (None, statistics)
    else:
        definition = None
        learner.add(next_test.trace())
        done = False
        learner_tests = [next_test]
        generated_tests = [next_test]
        last_ce = None
        ce = None
        while not done:
            if last_ce and ce == last_ce:
                raise Exception("Counterexample ", ce, " was not correctly processed")
            last_ce = ce
            start_time = int(time.time() * 1000)
            ret = learner.model(old_definition=definition)
            if ret is None:
                return (None, statistics)
            (model, definition) = ret
            end_time = int(time.time() * 1000)
            statistics.add_learning_time(end_time - start_time)
            done = True
            # we first check the tests that already have been generated
            for next_test in generated_tests:
                ce = next_test.check(model)
                if ce is not None:
                    print("CE: ", ce)
                    learner.add(ce)
                    done = False
                    break
            if not done:
                continue
            test_generator.initialize(model)

            if stats_tracker is not None:
                old_rsts = stats_tracker.resets()
                old_inputs = stats_tracker.inputs()

            # we then generate and check new tests, until either we find a CE,
            # or the suite is exhausted or we have run the intended number of tests
            for i in range(0, max_tests):
                next_test = test_generator.gen_test(model)
                if next_test is None:
                    break
                generated_tests.append(next_test)
                ce = next_test.check(model)
                if ce is not None:
                    print("CE: ", ce)
                    learner_tests.append(next_test)
                    learner.add(ce)
                    done = False
                    break
            test_generator.terminate()

            if stats_tracker is not None:
                statistics.resets = old_rsts
                statistics.inputs = old_inputs

        #print([str(test.trace() for test in learner_tests)])
        return (model, statistics)

def gen_blind_test(sut:SUT):
    """generates a sequence covering all input elements in the sut interface"""
    seq = []
    for abs_inp in sut.input_interface():
        cnt = 0
        # if it's RA stuff
        if isinstance(abs_inp, ActionSignature):
            if abs_inp.num_params == 0:
                val = None
            else:
                val = cnt
                cnt += 1
            seq.append(Action(abs_inp.label, val))
        elif isinstance(abs_inp, str):
            seq.append(abs_inp)
        else:
            raise Exception("Unrecognized type")
    obs = sut.run(seq)
    return obs.to_test()