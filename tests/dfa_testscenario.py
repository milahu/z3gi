import collections


"""Test scenarios contain a list of traces together with the number of locations and registers of the SUT generating
 these traces.
"""
DFATestCase = collections.namedtuple('DFATestCase', 'description traces nr_states')

# Define data
# 16 2
# 1 4 1 0 0 0
# 1 4 0 1 0 0
# 1 4 0 0 1 0
# 1 5 1 0 1 1 1
# 1 6 1 1 1 1 0 1
# 1 6 0 1 0 0 0 0
# 1 6 1 0 0 0 0 0
# 1 7 0 0 0 1 1 0 1
# 1 7 0 0 0 0 1 0 1
# 0 3 1 0 1
# 0 4 0 0 0 0
# 0 4 1 1 0 1
# 0 5 0 0 0 0 0
# 0 5 0 0 1 0 1
# 0 6 0 1 0 1 1 1
# 0 7 1 0 0 0 1 1 1

# store something and accept, as long as you give the stored value, accept, otherwise go back to start and reject
sut_m1 = DFATestCase("Abbadingo website example: This DFA accepts strings of 0's and 1's in which the number of 0's minus twice the number of 1's is either 1 or 3 more than a multiple of 5.",
                        [('1000', True),
                         ('0100', True),
                         ('0010', True),
                         ('10111', True),
                         ('111101', True),
                         ('010000', True),
                         ('100000', True),
                         ('0001101', True),
                         ('0000101', True),
                         ('101', False),
                         ('0000', False),
                         ('1101', False),
                         ('00000', False),
                         ('00101', False),
                         ('010111', False),
                         ('1000111', False),
                         ('', False)
                         ], 5)