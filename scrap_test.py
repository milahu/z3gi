from z3gi.learn.ra import RALearner
from tests.ra_testscenario import *
from encode.ra import RAEncoder


def check_ra_against_obs(learner, learned_ra, m,  test_scenario):
    """Checks if the learned RA corresponds to the scenario observations"""
    for trace, acc in test_scenario.traces:
        if learned_ra.accepts(trace) != acc:
            print(learner.encoder.tree)
            print("Register automaton {0} \n\n with model {1} \n doesn't correspond to the observation {2}"
                  .format(learned_ra, m, str((trace, acc))))
            return

for i in range(1,10):
    print("Experiment ",i)
    learner = RALearner(labels, encoder=RAEncoder())
    exp = sut_m5
    for trace in exp.traces:
        learner.add(trace)
    (_, ra, m) = learner._learn_model(exp.nr_locations,exp.nr_locations+1,exp.nr_registers)
    if m is not None:
        model = ra.export(m)
        loc = ra.locations
        lbl = ra.labels[labels[0]]
        fresh = ra.fresh
        check_ra_against_obs(learner, model, m, exp)
        print("Learning successful")
    else:
        print("unsat")