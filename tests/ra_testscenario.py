import collections

from z3gi.model.ra import Action

def act(val, label=None):
    if label is None:
        return Action("label", val)
    else:
        return Action(label, val)

"""Test scenarios contain a list of traces together with the number of locations and registers of the SUT generating
 these traces.
"""
RaTestScenario = collections.namedtuple('RaTestCase',
                                        ('traces',
                                    'nr_locations',
                                    'nr_registers'
                                    ))


# Define data

# store something and accept, as long as you give the stored value, accept, otherwise go back to start and reject
sut_m1 = RaTestScenario([([], False),
                         ([act(9)], True),
                         ([act(5), act(5)], True),
                         ([act(6), act(6)], True),
                         ([act(1), act(7)], False),
                         ([act(8), act(4)], False),
                         ([act(8), act(2), act(2)], True),
                         ([act(4), act(3), act(3), act(1)], False),
                         ([act(0), act(1), act(1), act(6), act(4)], True),
                         ([act(1), act(2), act(2), act(6), act(9), act(9)], True),
                         ([act(1), act(2), act(1)], True)
                         ], 2, 1)

# doing three transitions, and accept if the first and third parameters are the same
sut_m2 = RaTestScenario( [
    ([act(1)], True),
    ([act(1), act(1)], False),
    ([act(1), act(2)], False),
    ([act(1), act(1), act(1)], True),
    ([act(1), act(1), act(2)], False),
    ([act(1), act(2), act(1)], True),
    ([act(1), act(2), act(3)], False),
    ([act(1), act(1), act(1), act(1)], False),
    ([act(1), act(2), act(1), act(1)], False),
    ([act(1), act(1), act(2), act(1)], False),
    ([act(1), act(1), act(1), act(2)], False),
    # This is a check for Rick, ignore the traces below
    ([act(1), act(1), act(2), act(1), act(1)], False),
    ([act(1), act(1), act(2), act(1), act(2)], True)
], 3, 1)

# check for unique valuedness (non-UV 4 LOC, UV 5 LOC)
sut_m3 = RaTestScenario ([
   ([], False),
   ([act(1)], False),
   ([act(1), act(1)], False),
   ([act(1), act(2)], False),
   ([act(1), act(1), act(1)], True),
   ([act(1), act(2), act(1)], True),
   ([act(1), act(2), act(2)], True),
   ([act(1), act(2), act(3)], False),
   # add this and it's no longer SAT with 3 locations
   ([act(1), act(2), act(2), act(1), act(3)], True),
   ([act(1), act(1), act(1), act(1)], True),
   ([act(1), act(1), act(2), act(1)], True),
   ([act(0), act(1), act(2), act(2)], False),
   ([act(0), act(1), act(2), act(0)], True),
    ([act(0), act(1), act(2), act(1)], True),
   ([act(1), act(1), act(1), act(2)], True),
   ([act(1), act(1), act(1), act(1), act(2)], True),
   ([act(1), act(1), act(1), act(1), act(2), act(2)], True),
   ([act(1), act(1), act(1), act(2), act(2)], True),
   ([act(1), act(1), act(1), act(2), act(3)], True),
   ([act(1), act(2), act(2), act(2)], True),
   ([act(1), act(2), act(2), act(1)], True),
   ([act(1), act(2), act(3), act(4), act(1)], True),
   ([act(1), act(2), act(2), act(2), act(3)], True)
], 5, 2)

# check for non-shifting property (3 LOC NS, 4 LOC non-NS)
# expect this system to require one additional location than if our constraints allowed value shifting between registers
sut_m4 = RaTestScenario ([
   ([], False),
   ([act(1)], False),
   ([act(1), act(1)], False),
   ([act(1), act(2)], False),
   ([act(1), act(1), act(1)], False),
   ([act(1), act(2), act(1)], True),
   ([act(1), act(2), act(2)], False),
   ([act(1), act(2), act(3)], False),
   ([act(1), act(2), act(1), act(2)], True),
   ([act(1), act(2), act(1), act(1)], False),
   ([act(1), act(2), act(1), act(3)], False),
   ([act(1), act(2), act(1), act(3), act(3)], False),
   # add this and it is no longer SAT (for 3 locations)
   ([act(1), act(2), act(1), act(2), act(1)], True),
   ([act(1), act(2), act(1), act(3)], False),
   ([act(1), act(2), act(2), act(1)], False),
   ([act(1), act(2), act(1), act(1)], False),
   ([act(1), act(2), act(1), act(2)], True),
   ([act(1), act(2), act(1), act(2), act(1)], True),
   ([act(1), act(2), act(1), act(2), act(1), act(2)], True)
], 4, 2)

# Go to an accepting sink if the third value is different than the first two, else go to a rejecting sink
sut_m5 = RaTestScenario([
    ([], False),
    ([act(0)], False),
    ([act(0), act(0)], False),
    ([act(0), act(1)], False),
    ([act(0), act(0), act(0)], False),
    ([act(0), act(0), act(1)], True),
    ([act(0), act(1), act(0)], False),
    ([act(0), act(1), act(1)], False),
    ([act(0), act(1), act(2)], True),
    ([act(0), act(0), act(0), act(0)], False),
    ([act(0), act(0), act(0), act(1)], False),
    ([act(0), act(0), act(1), act(0)], True),
    ([act(0), act(0), act(1), act(1)], True),
    ([act(0), act(0), act(1), act(2)], True),
    ([act(0), act(1), act(0), act(0)], False),
    ([act(0), act(1), act(0), act(1)], False),
    ([act(0), act(1), act(0), act(2)], False),
    ([act(0), act(1), act(1), act(0)], False),
    ([act(0), act(1), act(1), act(1)], False),
    ([act(0), act(1), act(1), act(2)], False),
    ([act(0), act(1), act(2), act(0)], True),
    ([act(0), act(1), act(2), act(1)], True),
    ([act(0), act(1), act(2), act(2)], True),
    ([act(0), act(1), act(2), act(3)], True),
    ([act(0), act(0), act(0), act(0), act(0)], False),
    ([act(0), act(0), act(0), act(0), act(1)], False),
    ([act(0), act(0), act(0), act(1), act(0)], False),
    ([act(0), act(0), act(0), act(1), act(1)], False),
    ([act(0), act(0), act(0), act(1), act(2)], False),
    ([act(0), act(0), act(1), act(0), act(0)], True),
    ([act(0), act(0), act(1), act(0), act(1)], True),
    ([act(0), act(0), act(1), act(0), act(2)], True),
    ([act(0), act(0), act(1), act(1), act(0)], True),
    ([act(0), act(0), act(1), act(1), act(1)], True),
    ([act(0), act(0), act(1), act(1), act(2)], True),
    ([act(0), act(0), act(1), act(2), act(0)], True),
    ([act(0), act(0), act(1), act(2), act(1)], True),
    ([act(0), act(0), act(1), act(2), act(2)], True),
    ([act(0), act(0), act(1), act(2), act(3)], True),
    ([act(0), act(1), act(0), act(0), act(0)], False),
    ([act(0), act(1), act(0), act(0), act(1)], False),
    ([act(0), act(1), act(0), act(0), act(2)], False),
    ([act(0), act(1), act(0), act(1), act(0)], False),
    ([act(0), act(1), act(0), act(1), act(1)], False),
    ([act(0), act(1), act(0), act(1), act(2)], False),
    ([act(0), act(1), act(0), act(2), act(0)], False),
    ([act(0), act(1), act(0), act(2), act(1)], False),
    ([act(0), act(1), act(0), act(2), act(2)], False),
    ([act(0), act(1), act(0), act(2), act(3)], False),
    ([act(0), act(1), act(1), act(0), act(0)], False),
    ([act(0), act(1), act(1), act(0), act(1)], False),
    ([act(0), act(1), act(1), act(0), act(2)], False),
    ([act(0), act(1), act(1), act(1), act(0)], False),
    ([act(0), act(1), act(1), act(1), act(1)], False),
    ([act(0), act(1), act(1), act(1), act(2)], False),
    ([act(0), act(1), act(1), act(2), act(0)], False),
    ([act(0), act(1), act(1), act(2), act(1)], False),
    ([act(0), act(1), act(1), act(2), act(2)], False),
    ([act(0), act(1), act(1), act(2), act(3)], False),
    ([act(0), act(1), act(2), act(0), act(0)], True),
    ([act(0), act(1), act(2), act(0), act(1)], True),
    ([act(0), act(1), act(2), act(0), act(2)], True),
    ([act(0), act(1), act(2), act(0), act(3)], True),
    ([act(0), act(1), act(2), act(1), act(0)], True),
    ([act(0), act(1), act(2), act(1), act(1)], True),
    ([act(0), act(1), act(2), act(1), act(2)], True),
    ([act(0), act(1), act(2), act(1), act(3)], True),
    ([act(0), act(1), act(2), act(2), act(0)], True),
    ([act(0), act(1), act(2), act(2), act(1)], True),
    ([act(0), act(1), act(2), act(2), act(2)], True),
    ([act(0), act(1), act(2), act(2), act(3)], True),
    ([act(0), act(1), act(2), act(3), act(0)], True),
    ([act(0), act(1), act(2), act(3), act(1)], True),
    ([act(0), act(1), act(2), act(3), act(2)], True),
    ([act(0), act(1), act(2), act(3), act(3)], True),
    ([act(0), act(1), act(2), act(3), act(4)], True),
], 5, 2)

data_m6 = [
    ([], False),
    ([act(0)], True),
    ([act(0), act(0)], False),
    ([act(0), act(1)], False),
    #([act(0), act(0), act(0)], ???),
    ([act(0), act(0), act(1)], False),
    ([act(0), act(1), act(0)], True),
    ([act(0), act(1), act(1)], False),
    ([act(0), act(1), act(2)], False),
    #([act(0), act(0), act(0), act(0)], ???),
    #([act(0), act(0), act(0), act(1)], ???),
    #([act(0), act(0), act(1), act(0)], ???),
    ([act(0), act(0), act(1), act(1)], False),
    ([act(0), act(0), act(1), act(2)], False),
    ([act(0), act(1), act(0), act(0)], False),
    ([act(0), act(1), act(0), act(1)], True),
    ([act(0), act(1), act(0), act(2)], False),
    ([act(0), act(1), act(1), act(0)], True),
    ([act(0), act(1), act(1), act(1)], True),
    ([act(0), act(1), act(1), act(2)], True),
    ([act(0), act(1), act(2), act(0)], True),
    ([act(0), act(1), act(2), act(1)], False),
    ([act(0), act(1), act(2), act(2)], False),
    ([act(0), act(1), act(2), act(3)], False),
]

data_m7 = [
    ([], False),
    ([act(0)], False),
    ([act(0), act(0)], False),
    ([act(0), act(1)], False),
    ([act(0), act(0), act(0)], False),
    ([act(0), act(0), act(1)], True),
#    ([act(0), act(1), act(0)], False),
#    ([act(0), act(1), act(1)], False),
#    ([act(0), act(1), act(2)], True),
]


