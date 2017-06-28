import collections

from z3gi.model.ra import Action

labels = ["in"]
outputs = ["OK", "NOK"]

def act(val, label=None):
    if label is None:
        return Action(labels[0], val)
    else:
        return Action(label, val)



"""Test scenarios contain a list of traces together with the number of locations and registers of the SUT generating
 these traces.
"""
RaTestScenario = collections.namedtuple('RaTestCase',
                                        ('description',
                                            'traces',
                                    'nr_locations',
                                    'nr_registers'
                                    ))

# Define data

sut_m1 = RaTestScenario("Accept everything", [
    [(act(0, 'in'), act(100, 'OK'))],
    [(act(0, 'in'), act(101, 'OK')), (act(0, 'in'), act(102, 'OK'))]
    ],
    4, 1
)

# IO
sut_m2 = RaTestScenario( "Store value and produce OK output if you get that same value", [
    [(act(0, 'in'), act(100, 'OK')), (act(0, 'in'), act(101, 'OK')), (act(0, 'in'), act(102, 'OK')), (act(0, 'in'), act(103, 'OK'))],
    [(act(0, 'in'), act(100, 'OK')), (act(0, 'in'), act(101, 'OK')), (act(0, 'in'), act(102, 'OK')), (act(1, 'in'), act(103, 'NOK'))],
    [(act(0, 'in'), act(100, 'OK')), (act(0, 'in'), act(101, 'OK')), (act(1, 'in'), act(102, 'NOK')), (act(0, 'in'), act(103, 'OK'))],
    [(act(0, 'in'), act(100, 'OK')), (act(1, 'in'), act(101, 'NOK')), (act(0, 'in'), act(102, 'OK')), (act(0, 'in'), act(103, 'OK'))],
    [(act(1, 'in'), act(100, 'NOK')), (act(0, 'in'), act(101, 'OK')), (act(0, 'in'), act(102, 'OK')), (act(0, 'in'), act(103, 'OK'))]],
                          20, 2)
