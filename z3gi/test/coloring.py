from typing import Set

from model import Automaton, Transition
from sut.sut_cache import Cache
from test import TestGenerator
"""Explores all transitions in a model that have not been explored (or colored) during test execution. """


class ColoringTestGenerator(TestGenerator):
    def __init__(self, sut, cache:Cache):
        self._sut = sut
        self._cache = cache
        self._test_seq = []

    def initialize(self, model: Automaton):
        colored_trans = self._colored_transitions(model)
        all_trans = set([trans for state in model.states() for trans in model.transitions(state)])
        # these are all the transitions we want to navigate
        uncolored_transitions = all_trans.difference(colored_trans)
        colored_acc_seq = get_colored_trans_seq(model, colored_trans)
        for trans in uncolored_transitions:
            if trans.start_state not in colored_acc_seq:
                print(len(colored_trans), " colored transitions:", list(map(str, colored_trans)))
                print(len(uncolored_transitions), " uncolored transitions:", list(map(str, uncolored_transitions)))
                print(self._cache._tree)
                print(model)
                exit(0)

            colored_path = colored_acc_seq[trans.start_state]
            # the path includes the transition we want to color
            trans_path = colored_path + [trans]
            self._test_seq.append(model.trans_to_inputs(trans_path))

    def _colored_transitions(self, model: Automaton) -> Set[Transition]:
        trans = set()
        for obs in self._cache.obs_iterator():
            colored_trans = model.inputs_to_trans(obs.inputs())
            trans = trans.union(set(colored_trans))
        return trans

    def gen_test(self, model: Automaton):
        if len(self._test_seq) > 0:
            obs = self._sut.run(self._test_seq.pop())
            return obs.to_test()
        else:
            return None

    def terminate(self):
        self._test_seq = []


def get_colored_trans_seq(aut : Automaton, colored_trans):
    """Returns a dictionary of access sequences comprising only colored transitions"""
    to_visit = [([], aut.start_state())]
    acc_trans_seq  = dict()
    while len(to_visit) > 0:
        (col_seq, state) = to_visit.pop()
        acc_trans_seq[state] = col_seq
        next_transitions = (trans for trans in
                            colored_trans.
                            intersection(set(aut.transitions(state)))
                            if trans.end_state not in acc_trans_seq)
        for next_trans in next_transitions:
            next_seq = col_seq + [next_trans]
            to_visit.append((next_seq, next_trans.end_state))
    return acc_trans_seq


