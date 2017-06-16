# Improved encoding
import collections

import itertools
import z3

num_locations = 2
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
Register, registers = enum('Register', ['register{0}'.format(i) for i in range(num_registers)] + ['perp'])
perp = registers[-1]

Value = z3.DeclareSort('Value')
Node = z3.DeclareSort('Node')



RegisterAutomaton = collections.namedtuple('RegisterAutomaton',
                                           'start transition output guard update')

def register_automaton(Location, Label, Register, start):
    return RegisterAutomaton(start = start,
                             # For r != perp, transition(q, l, r) only makes sense if guard(q, l, r) == true.
                             # In this case there is a transition q -- l(v), v==r -> transition(q, l, r),
                             # Otherwise, use q -- l(v), perp -> transition(q, l, perp).
                             transition = z3.Function('transition', Location, Label, Register, Location),
                             # If there is an l such that guard(q, l, r) == True, then used(q, r) == true.
                             guard=z3.Function('guard', Location, Label, Register, z3.BoolSort()),
                             # TODO: does used still make sense if we have guard?
                             # TODO: does used make sense at all?
                             # Since we can't lose registers, there will never be transitions (back) to states that use less registers
                             # Can't we just assume all registers are used all the time, but sometimes we don't care what's in them?
                             #used = z3.Function('used', Location, Register, z3.BoolSort()),
                             # !!!! if update(q, l) = r, then (for all r', r'!= fresh -> guard(q, l, r') == False)
                             update = z3.Function('update', Location, Label, Register),
                             output=z3.Function('output', Location, z3.BoolSort()),
                             )

Mapper = collections.namedtuple('Mapper',
                               'map valuation')

def mapper(Node, Location, Value, Register):
    return Mapper(map = z3.Function('map', Node, Location),
                  valuation = z3.Function('valuation', Node, Register, Value))

Action = collections.namedtuple('Action',
                                'label value')

label = labels[0]

act = lambda x: Action(label, x)

def determinize(seq):
    neat = {}
    i = 0
    for action in seq:
        if action.value not in neat:
            neat[action.value] = z3.Const('val{0}'.format(i), Value)
            i = i + 1
    return [Action(action.label, neat[action.value]) for action in seq]


# Trie data structure
class Trie(object):
    def __init__(self, counter):
        self.id = next(counter)
        self.node = z3.Const('node{0}'.format(self.id), Node)
        self.counter = counter
        self.children = {}

    def __getitem__(self, seq):
        seq = determinize(seq)
        trie = self
        for action in seq:
            if action not in trie.children:
                trie.children[action] = Trie(self.counter)
            trie = trie.children[action]
        return trie

    def __iter__(self):
        yield self
        for child in itertools.chain(*map(iter, self.children.values())):
            yield child

    def transitions(self):
        for node in self:
            for action in node.children:
                yield node, action, node.children[action]

trie = Trie(itertools.count(0))

ra = register_automaton(Location, Label, Register, locations[0])
m = mapper(Node, Location, Value, Register)


q = z3.Const('q', Location)
l = z3.Const('l', Label)
r = z3.Const('r', Register)
rp = z3.Const('rp', Register)
n = z3.Const('n', Node)
np = z3.Const('np', Node)
v = z3.Const('v', Value)
init = z3.Const('init', Value)
root = trie.node


# Axioms
axioms = [
    # if update(q, l) = r, then (for all r', r'!= perp -> guard(q, l, r') == False)
    # q -- l(p) r := p -> q' then  q -- l(p) r == p -> q'' if q' != q'' is problematic
    z3.ForAll([q, l, r],
              z3.Implies(ra.update(q, l) == r,
                         z3.ForAll([rp],
                                   z3.Implies(rp != perp,
                                              ra.guard(q, l, rp) == False # THIS IS WRONG, WE ALSO NEED VALUATION
                                              )
                                   )
                         )
              ),

    # If we update a non-fresh register on a transition from a state,
    # then the register is assigned the value.
    # Else, the register keeps its previous value.
    z3.ForAll([n, np, r, v, l],
              z3.Implies(ra.transition(m.map(n), l, r) == m.map(np),
                         z3.If(r != perp,
                               z3.Implies(m.valuation(np, r) != m.valuation(n, r),
                                          ra.update(m.map(n), l) == r),
                               m.valuation(np, r) == m.valuation(n, r)
                               )
                         )
              ),

    # In the start state of the mapper,
    # all registers contain a value outside the domain of plausible values.
    z3.ForAll([r],
              z3.Implies(r != perp,
                         m.valuation(root, r) == init)
              ),
]






# Define data
data = [([act(5), act(5)], True),
        ([act(6), act(6)], True),
        ([act(1), act(7)], False),
        ([act(9)], True),
        ([act(8), act(4)], False),
        ([act(8), act(2), act(2)], True),
        ([act(4), act(3), act(3), act(1)], False),
        ([act(0), act(1), act(1), act(6), act(4)], True),
        ([act(1), act(2), act(2), act(6), act(9), act(9)], True),
        ]


# Add output constraints for data
output_constraints = []
for seq, accept in data:
    node = trie[seq]
    output_constraints.append(ra.output(m.map(node.node)) == accept)


# Add transition constraints for all transitions in trie
transition_constraints = [ra.start == m.map(trie.node)]
for n, a, c in trie.transitions():
    transition_constraints.append(z3.Exists([r], ra.transition(m.map(n.node), a.label, r) == m.map(c.node)))


# Create an empty value and assert that all (neat) values are different
values = {init}
for n, a, c in trie.transitions():
    values.add(a.value)

distinct_values = z3.Distinct(list(values))

s = z3.Solver()
s.add(axioms)
s.add(transition_constraints)
s.add(output_constraints)
s.add(distinct_values)

print(s.check())
model = s.model()
print(model)
for seq, accept in data:
    print(model.eval(ra.output(m.map(trie[seq].node)) == accept))
for n in trie:
    print('{0} maps to {1}'.format(n.node, model.eval(m.map(n.node))))
