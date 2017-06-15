# Improved encoding
import collections
import z3

num_locations = 3
num_labels = 1
num_registers = 1

def enum(type, names):
    dt = z3.Datatype(type)
    for name in names:
        dt.declare(name)
    dt = dt.create()
    fields = [dt.__getattribute__(name) for name in names]
    return (dt, fields)

Location, locations = enum('Location', ['location{0}'.format(i) for i in range(num_locations)])
Label, labels = enum('Label', ['label{0}'.format(i) for i in range(num_labels)])
Register, registers = enum('Register', ['register{0}'.format(i) for i in range(num_registers)] + ['fresh'])

Value = z3.DeclareSort('Value')
Node = z3.DeclareSort('Node')



RegisterAutomaton = collections.namedtuple('RegisterAutomaton',
                                           'start transition output used update')

def register_automaton(Location, Label, Register, start):
    return RegisterAutomaton(start = start,
                             transition = z3.Function('transition', Location, Label, Register, Location),
                             output = z3.Function('output', Location, z3.BoolSort()),
                             used = z3.Function('used', Location, Register, z3.BoolSort()),
                             update = z3.Function('update', Location, Label, Register))

Mapper = collections.namedtuple('Mapper',
                               'map valuation')

def mapper(Node, Location, Value, Register):
    return Mapper(map = z3.Function('map', Node, Location),
                  valuation = z3.Function('valuation', Node, Value, Register))

ra = register_automaton(Location, Label, Register, locations[0])
m = mapper(Node, Location, Value, Register)


q = z3.Const('q', Location)
l = z3.Const('l', Label)
r = z3.Const('r', Register)
rp = z3.Const('rp', Register)
fresh = registers[-1]

# Register automaton axioms
ra_axioms = [
    # Updating a non-fresh register for a label in a location,
    # means that the register is used in any location reached from this location with a fresh guard.
    z3.ForAll([q, l, r],
              z3.Implies(z3.And(ra.update(q, l) == r, r != fresh),
                         ra.used(ra.transition(q, l, fresh) == r))),
    # If a non-fresh register is used in a state,
    # it was either used in the previous state,
    # or it was updated on the previous transition.
    z3.ForAll([q, l, r, rp],
              z3.Implies(ra.used(ra.transition(q, l, rp), r) == True,
                         z3.Or(ra.used(q, r) == True,
                               z3.And(ra.update(q, l) == r,
                                      rp == fresh)))),
    # None of the registers are in use in the start state.
    z3.ForAll([r],
              ra.used(ra.start, r) == False)
    ]

n = z3.Const('n', Node)
np = z3.Const('np', Node)
v = z3.Const('v', Value)

# Mapper axioms
m_axioms = [
    # If we update a register on a transition from a state,
    # then the register is assigned the value.
    # Else, the register keeps its previous value.
    z3.ForAll([n, np, r, v, l],
              z3.If(z3.And(ra.transition(m.map(n), l, r) == m.map(np),
                           ra.update(m.map(n), l) == r),
                    m.valuation(np, v) == r,
                    m.valuation(np, v) == m.valuation(n, v))),
    # If there is a transition from a state, label and (non-fresh) register,
    # then the valuation of that register should be kept.
    z3.ForAll([n, np, l, r, v],
              z3.Implies(z3.And(ra.transition(m.map(n), l, r) == m.map(np),
                                r != fresh),
                         m.valuation(n, v) == r))
    ]



