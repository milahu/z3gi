import itertools

from model.ra import IORegisterAutomaton
from utils import determinize
from z3gi.learn.ra import RALearner
from tests.iora_testscenario import *
from encode.iora import IORAEncoder
from model.parsing import to_dot

def determinize_act_io(tuple_seq):
    seq = list(itertools.chain.from_iterable(tuple_seq))
    det_seq = determinize(seq)
    det_act_seq = [Action(l, v) for (l, v) in det_seq]
    det_duple_seq = [(det_act_seq[i], det_act_seq[i+1]) for i in range(0, len(det_act_seq), 2)]
    return det_duple_seq

def check_ra_against_obs(learner: RALearner, learned_ra:IORegisterAutomaton, m, test_scenario: RaTestScenario):
    """Checks if the learned RA corresponds to the scenario observations"""
    for trace in test_scenario.traces:
        trace = determinize_act_io(trace)
        inp_trace = []
        for (inp_act, out_act) in trace:
            inp_trace.append(inp_act)
            output = learned_ra.output(inp_trace)

            if output != out_act:
                print("Register automaton: \n {0} \n with model: \n {1} \n responds to {2} "
                      "with {3} instead of {4}".format(learned_ra, m, inp_trace, output, out_act))
                return

for i in range(1,2):
    print("Experiment ",i)
    learner = RALearner(IORAEncoder(), verbose=True)
    exp = sut_m6
    for trace in exp.traces:
        learner.add(trace)
    (_, ra, m) = learner._learn_model(exp.nr_locations-1,exp.nr_locations+1,exp.nr_registers)
    if m is not None:
        model = ra.export(m)
        print(model)
        check_ra_against_obs(learner, model, m, exp)
    else:
        print("unsat")