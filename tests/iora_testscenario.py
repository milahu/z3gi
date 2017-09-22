import collections

from z3gi.model.ra import Action

labels = ["in"]
outputs = ["OK", "NOK"]

def act(val, label=None):
    if label is None:
        return Action(labels[0], val)
    else:
        return Action(label, val)

def io(val, label, oval, output):
    return (act(val, label), act(oval, output))

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
    2, 1
)

sut_m2 = RaTestScenario("OK first then always NOK", [
    [io(0, 'in', 100, 'OK')],
    [io(0, 'in', 100, 'OK'), io(0, 'in', 101, 'NOK')],
    [io(0, 'in', 100, 'OK'), io(1, 'in', 101, 'NOK')],
    [io(0, 'in', 100, 'OK'), io(1, 'in', 101, 'NOK')],
    [io(0, 'in', 100, 'OK'), io(0, 'in', 101, 'NOK'), io(0, 'in', 102, 'NOK')],
    [io(0, 'in', 100, 'OK'), io(0, 'in', 101, 'NOK'), io(1, 'in', 102, 'NOK')],
    [io(0, 'in', 100, 'OK'), io(0, 'in', 101, 'NOK'), io(2, 'in', 102, 'NOK')],
    [io(0, 'in', 100, 'OK'), io(1, 'in', 101, 'NOK'), io(0, 'in', 102, 'NOK')],
    [io(0, 'in', 100, 'OK'), io(1, 'in', 101, 'NOK'), io(1, 'in', 102, 'NOK')],
    [io(0, 'in', 100, 'OK'), io(1, 'in', 101, 'NOK'), io(2, 'in', 102, 'NOK')],
    ],
                        4, 1)

sut_m3 = RaTestScenario("Alternating OK/NOK", [
    [io(0, 'in', 100, 'OK')],
    [io(0, 'in', 100, 'OK'), io(0, 'in', 101, 'NOK')],
    [io(0, 'in', 100, 'OK'), io(1, 'in', 101, 'NOK')],
    [io(0, 'in', 100, 'OK'), io(1, 'in', 101, 'NOK')],
    [io(0, 'in', 100, 'OK'), io(0, 'in', 101, 'NOK'), io(0, 'in', 102, 'OK')],
    [io(0, 'in', 100, 'OK'), io(0, 'in', 101, 'NOK'), io(1, 'in', 102, 'OK')],
    [io(0, 'in', 100, 'OK'), io(0, 'in', 101, 'NOK'), io(2, 'in', 102, 'OK')],
    [io(0, 'in', 100, 'OK'), io(1, 'in', 101, 'NOK'), io(0, 'in', 102, 'OK')],
    [io(0, 'in', 100, 'OK'), io(1, 'in', 101, 'NOK'), io(1, 'in', 102, 'OK')],
    [io(0, 'in', 100, 'OK'), io(1, 'in', 101, 'NOK'), io(2, 'in', 102, 'OK')],
    ],
                        4, 1)

# IO
sut_m4 = RaTestScenario( "Store value and produce OK output if you get that same value", [
    [(act(0, 'in'), act(100, 'OK')), (act(0, 'in'), act(101, 'OK')), (act(0, 'in'), act(102, 'OK')), (act(0, 'in'), act(103, 'OK'))],
    [(act(0, 'in'), act(100, 'OK')), (act(0, 'in'), act(101, 'OK')), (act(0, 'in'), act(102, 'OK')), (act(1, 'in'), act(103, 'NOK'))],
    [(act(0, 'in'), act(100, 'OK')), (act(0, 'in'), act(101, 'OK')), (act(1, 'in'), act(102, 'NOK')), (act(0, 'in'), act(103, 'OK'))],
    [(act(0, 'in'), act(100, 'OK')), (act(1, 'in'), act(101, 'NOK')), (act(0, 'in'), act(102, 'OK')), (act(0, 'in'), act(103, 'OK'))],
  #  [(act(1, 'in'), act(100, 'NOK')), (act(0, 'in'), act(101, 'OK')), (act(0, 'in'), act(102, 'OK')), (act(0, 'in'), act(103, 'OK'))]],
                         ],
                         6, 2)

# login model (incomplete traces)
sut_m5 = RaTestScenario("Login model", [
    [io(0, 'reg', 100, 'OK') ],
    [io(0, 'in', 100, 'NOK') ],
    [io(0, 'out', 100, 'NOK') ],
    [io(0, 'reg', 100, 'OK'), io(1, 'reg', 101, 'NOK')],
    [io(0, 'reg', 100, 'OK'), io(1, 'in', 101, 'NOK') ],
    [io(0, 'reg', 100, 'OK'), io(0, 'in', 101, 'OK')  ],
    [io(0, 'reg', 100, 'OK'), io(1, 'out', 101, 'NOK')],
    [io(0, 'in', 100, 'NOK'), io(0, 'reg', 101, 'OK') ],
    [io(0, 'in', 100, 'NOK'), io(0, 'in', 101, 'NOK') ],
    [io(0, 'in', 100, 'NOK'), io(0, 'out', 101, 'NOK')],
    [io(0, 'out', 100, 'NOK'), io(1, 'reg', 101, 'OK') ],
    [io(0, 'out', 100, 'NOK'), io(1, 'in', 101, 'NOK') ],
    [io(0, 'out', 100, 'NOK'), io(1, 'out', 101, 'NOK')],

    [io(0, 'reg', 100, 'OK'), io(0, 'in', 101, 'OK'), io(1, 'reg', 102, 'NOK')],
    [io(0, 'reg', 100, 'OK'), io(0, 'in', 101, 'OK'), io(1, 'in', 102, 'NOK')],
    [io(0, 'reg', 100, 'OK'), io(0, 'in', 101, 'OK'), io(0, 'in', 102, 'NOK')],
    [io(0, 'reg', 100, 'OK'), io(0, 'in', 101, 'OK'), io(1, 'out', 102, 'NOK')],
    [io(0, 'reg', 100, 'OK'), io(0, 'in', 101, 'OK'), io(0, 'out', 102, 'OK')],

    [io(0, 'reg', 100, 'OK'), io(0, 'in', 101, 'OK'), io(1, 'reg', 102, 'NOK'), io(2, 'reg', 103, 'NOK')],
    [io(0, 'reg', 100, 'OK'), io(0, 'in', 101, 'OK'), io(1, 'reg', 102, 'NOK'), io(2, 'in',  103, 'NOK') ],
    [io(0, 'reg', 100, 'OK'), io(0, 'in', 101, 'OK'), io(1, 'reg', 102, 'NOK'), io(0, 'out', 103, 'OK')],
    [io(0, 'reg', 100, 'OK'), io(0, 'in', 101, 'OK'), io(1, 'reg', 102, 'NOK'), io(2, 'out', 103, 'NOK')],

    [io(0, 'reg', 100, 'OK'), io(0, 'in', 101, 'OK'), io(1, 'in', 102, 'NOK'), io(2, 'reg', 103, 'NOK')],
    [io(0, 'reg', 100, 'OK'), io(0, 'in', 101, 'OK'), io(1, 'in', 102, 'NOK'), io(2, 'in',  103, 'NOK') ],
    [io(0, 'reg', 100, 'OK'), io(0, 'in', 101, 'OK'), io(1, 'in', 102, 'NOK'), io(0, 'out', 103, 'OK')],
    [io(0, 'reg', 100, 'OK'), io(0, 'in', 101, 'OK'), io(1, 'in', 102, 'NOK'), io(2, 'out', 103, 'NOK')],

    [io(0, 'reg', 100, 'OK'), io(0, 'in', 101, 'OK'), io(1, 'out', 102, 'NOK'), io(2, 'reg', 103, 'NOK')],
    [io(0, 'reg', 100, 'OK'), io(0, 'in', 101, 'OK'), io(1, 'out', 102, 'NOK'), io(2, 'in',  103, 'NOK') ],
    [io(0, 'reg', 100, 'OK'), io(0, 'in', 101, 'OK'), io(1, 'out', 102, 'NOK'), io(0, 'out', 103, 'OK')],
    [io(0, 'reg', 100, 'OK'), io(0, 'in', 101, 'OK'), io(1, 'out', 102, 'NOK'), io(2, 'out', 103, 'NOK')],

    [io(0, 'reg', 100, 'OK'), io(0, 'in', 101, 'OK'), io(0, 'out', 102, 'OK'), io(1, 'reg', 103, 'NOK')],
    [io(0, 'reg', 100, 'OK'), io(0, 'in', 101, 'OK'), io(0, 'out', 102, 'OK'), io(1, 'in',  103, 'NOK') ],
    [io(0, 'reg', 100, 'OK'), io(0, 'in', 101, 'OK'), io(0, 'out', 102, 'OK'), io(0, 'in',  103, 'OK')],
    [io(0, 'reg', 100, 'OK'), io(0, 'in', 101, 'OK'), io(0, 'out', 102, 'OK'), io(1, 'out', 103, 'NOK')],

    [io(0, 'reg', 100, 'OK'), io(0, 'in', 101, 'OK'), io(0, 'out', 102, 'OK'), io(1, 'reg', 103, 'NOK'), io(0, 'in',  104, 'OK')],
    [io(0, 'reg', 100, 'OK'), io(0, 'in', 101, 'OK'), io(0, 'out', 102, 'OK'), io(1, 'out', 103, 'NOK'), io(0, 'in',  104, 'OK')],

    ],
                        9, 1)

# login model (incomplete traces)
sut_m6 = RaTestScenario("Stack model", [
    [io(0, 'put', None, 'OK') ],
    [io(None, 'get', None, 'NOK') ],
    [io(0, 'put', None, 'OK'), io(1, 'put', None, 'NOK') ],
    [io(0, 'put', None, 'OK'), io(None, 'get', 0, 'oget') ],
    [io(None, 'get', None, 'NOK'), io(0, 'put', None, 'OK')],
    [io(None, 'get', None, 'NOK'), io(None, 'get', None, 'NOK')],
    [io(0, 'put', None, 'OK'), io(None, 'get', 0, 'oget'), io(None, 'get', None, 'NOK') ],
    [io(0, 'put', None, 'OK'), io(None, 'get', 0, 'oget'), io(1, 'put', None, 'OK') ],
    [io(0, 'put', None, 'OK'), io(None, 'get', 0, 'oget'), io(None, 'get', None, 'NOK') ],
    [io(0, 'put', None, 'OK') ],
    ], 6, 1)


sut_m7 = RaTestScenario("Accept everything. Return same output", [
    [io(0, 'in', 0, 'OK')],
    [io(0, 'in', 0, 'OK'), io(0, 'in', 0, 'OK')],
    [io(0, 'in', 0, 'OK'), io(1, 'in', 1, 'OK')]
    ], 3, 1)


sut_m8 = RaTestScenario("Accept everything. None output", [
    [io(0, 'in', None, 'OK')],
    [io(0, 'in', None, 'OK'), io(0, 'in', None, 'OK')],
    [io(0, 'in', None, 'OK'), io(1, 'in', None, 'OK')]
    ], 3, 1)

sut_m9 = RaTestScenario("Accept everything. None input", [
    [io(None, 'in', 0, 'OK')],
    [io(None, 'in', 0, 'OK'), io(None, 'in', 1, 'OK')],
], 3, 1)