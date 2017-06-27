from z3gi.learn.ra import RALearner
from tests.ra_testscenario import sut_m3, labels


def check_ra_against_obs(learned_ra, m,  test_scenario):
    """Checks if the learned RA corresponds to the scenario observations"""
    for trace, acc in test_scenario.traces:
        if learned_ra.accepts(trace) != acc:
            print("Register automaton {0} \n\n with model {1} \n doesn't correspond to the observation {2}"
                  .format(learned_ra, m, str((trace, acc))))
            return

for _ in range(1,50):
    learner = RALearner(labels)
    exp = sut_m3
    for trace in exp.traces:
        learner.add(trace)
    (_, ra, m) = learner._learn_model(4,4,2)
    model = ra.export(m)
    loc = ra.locations
    lbl = ra.labels[labels[0]]
    fresh = ra.fresh
    check_ra_against_obs(model, m, exp)