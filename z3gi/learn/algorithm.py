import copy
from typing import List, Tuple, Union,cast

from model import Automaton
from learn import Learner
from model.fa import State
from model.ra import Action
from sut import StatsTracker, SUT, NoRstSUT
from sut.scalable import ActionSignature
from sut.simulation import get_no_rst_simulation
from test import TestGenerator, Test
import utils
import time

__all__ = [
    "learn",
    "learn_mbt",
    "learn_no_reset"
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
        test = cast(Test, test_type(traces.pop(0)))
        definition = None
        learner.add(test.tr)
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
                    print("CE: ", ce)
                    learner.add(ce)
                    done = False
                    break
        return (model, statistics)
import model
def _next_seq_rwalkfromstate(aut:Automaton, input_seq, rand_seq=3):
    state = aut.state(input_seq)
    acc_seq = model.get_trans_acc_seq(aut, from_state=state)
    next_state = utils.rand_sel(list(acc_seq.keys()))
    next_seq = acc_seq[next_state]
    for _ in range(0, rand_seq):
        tr = utils.rand_sel(aut.transitions(state))
        state = tr.end_state
        next_seq.append(tr)
    return aut.trans_to_inputs(next_seq)

def _next_seq_rwalk(aut:Automaton, input_seq, rand_seq=3):
    return [utils.rand_sel(aut.input_labels()) for _ in range(0, rand_seq)]

def learn_no_reset(sut:NoRstSUT, learner:Learner, max_inputs:int, rand_seq=3) -> Tuple[Union[Automaton, None], Statistics]:
    """ takes a non-reseting SUL, a learner, a test generator, and a bound on the number of inputs and generates a model"""
    trace = []
    alpha = sut.input_interface()
    seq = gen_blind_seq(sut)
    statistics = Statistics()
    trace.extend(sut.steps(seq))
    learner.add(list(trace))
    start_time = int(time.time() * 1000)
    (hyp, definition) = learner.model()
    end_time = int(time.time() * 1000)
    statistics.add_learning_time(end_time - start_time)
    done = False
    while not done:
        sim = get_no_rst_simulation(hyp)
        inputs = [inp for (inp, _) in trace]
        sim.steps(inputs)
        next_inputs = _next_seq_rwalkfromstate(hyp, inputs, rand_seq=rand_seq)
        done = True
        for _ in range(0, max_inputs):
            if len(next_inputs) == 0:
                next_inputs = _next_seq_rwalkfromstate(hyp, inputs, rand_seq=rand_seq)
            rand_inp = next_inputs.pop(0)
            #rand_inp = utils.rand_sel(alpha)
            out_sut = sut.step(rand_inp)
            trace.append((rand_inp, out_sut))
            inputs.append(rand_inp)
            out_hyp = sim.step(rand_inp)
            if out_sut != out_hyp:
                learner.add(list(trace))
                start_time = int(time.time() * 1000)
                ret = learner.model(old_definition=definition)
                if ret is None:
                    return  None, statistics
                hyp,definition = ret
                end_time = int(time.time() * 1000)
                statistics.add_learning_time(end_time - start_time)
                print("new hyp")
                done = False
                break
    statistics.inputs = len(trace) - max_inputs
    return hyp, statistics

def learn_mbt(sut:SUT, learner:Learner, test_generator:TestGenerator, max_tests:int, stats_tracker:StatsTracker=None) -> Tuple[Union[Automaton, None], Statistics]:
    """ takes learner, a test generator, and bound on the number of tests and generates a model"""
    next_test = gen_blind_test(sut)
    statistics = Statistics()
    model = None
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
                print(model)
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

def gen_blind_seq(sut):
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
    return seq