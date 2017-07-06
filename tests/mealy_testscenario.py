

import collections

from z3gi.model.ra import Action



"""Test scenarios contain a list of traces together with the number of locations and registers of the SUT generating
 these traces.
"""
MealyTestCase = collections.namedtuple('MealyTestCase', 'description traces nr_states')

sut_m1 = MealyTestCase("output '1' if the length of the trace so far is even, else output '0'",
                        [(('a', '0'), ('a', '1'), ('a', '0'), ('a', '1')),
                         (('a', '0'), ('a', '1'), ('a', '0'), ('b', '1')),
                         (('a', '0'), ('a', '1'), ('b', '0'), ('a', '1')),
                         (('a', '0'), ('b', '1'), ('a', '0'), ('a', '1')),
                         (('b', '0'), ('a', '1'), ('a', '0'), ('a', '1')),
                         (('a', '0'), ('a', '1'), ('b', '0'), ('b', '1')),
                         (('a', '0'), ('b', '1'), ('b', '0'), ('a', '1')),
                         (('b', '0'), ('b', '1'), ('a', '0'), ('a', '1')),
                         (('a', '0'), ('b', '1'), ('b', '0'), ('b', '1')),
                         (('b', '0'), ('b', '1'), ('b', '0'), ('a', '1')),
                         (('b', '0'), ('b', '1'), ('b', '0'), ('b', '1')),
                         ], 2)