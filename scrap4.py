# WORKING! encoding
import collections

import itertools
import z3

num_locations = 4
num_registers = 2

def enum(type, names):
    dt = z3.Datatype(type)
    for name in names:
        dt.declare(name)
    dt = dt.create()
    fields = [dt.__getattribute__(name) for name in names]
    return (dt, fields)

Location, locations = enum('Location', ['location{0}'.format(i) for i in range(num_locations)])
Register, registers = enum('Register', ['register{0}'.format(i) for i in range(num_registers)] + ['fresh'])
fresh = registers[-1]

Value = z3.DeclareSort('Value')
Node = z3.DeclareSort('Node')



RegisterAutomaton = collections.namedtuple('RegisterAutomaton',
                                           'start transition output guard update')

def register_automaton(Location, Register, start):
    return RegisterAutomaton(start = start,
                             # For r != fresh, transition(q, l, r) only makes sense if guard(q, l, r) == true.
                             # In this case there is a transition q -- l(v), v==r -> transition(q, l, r),
                             # Otherwise, use q -- l(v), fresh -> transition(q, l, fresh).
                             transition = z3.Function('transition', Location, Register, Location),
                             guard=z3.Function('guard', Location, Register, z3.BoolSort()),
                             update = z3.Function('update', Location, Register, Register),
                             output=z3.Function('output', Location, z3.BoolSort()),
                             )

Mapper = collections.namedtuple('Mapper',
                               'map val')

def mapper(Node, Location, Value, Register):
    return Mapper(map = z3.Function('map', Node, Location),
                  val = z3.Function('valuation', Node, Register, Value))

Action = collections.namedtuple('Action',
                                'value')

act = lambda x: Action(x)

def determinize(seq):
    neat = {}
    i = 0
    for action in seq:
        if action.value not in neat:
            neat[action.value] = z3.Const('val{0}'.format(i), Value)
            i = i + 1
    return [Action(neat[action.value]) for action in seq]


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

ra = register_automaton(Location, Register, locations[0])
m = mapper(Node, Location, Value, Register)


q = z3.Const('q', Location)
r = z3.Const('r', Register)
rp = z3.Const('rp', Register)
# n = z3.Const('n', Node)
# np = z3.Const('np', Node)
# v = z3.Const('v', Value)
init = z3.Const('init', Value)
root = trie.node


# Axioms
axioms = [

    z3.ForAll([q],
              ra.guard(q, fresh) == True
              ),

    z3.ForAll([q, r, rp],
              z3.Implies(z3.And(r != fresh,
                                ra.update(q, rp) == r),
                         rp == fresh
                         )
              ),

    # In the start state of the mapper,
    # all registers contain a value outside the domain of plausible values.
    z3.ForAll([r],
              z3.Implies(r != fresh,
                         m.val(root, r) == init)
              ),

    z3.ForAll([q, r],
              z3.Implies(z3.And(r != fresh,
                                ra.transition(q, fresh) == ra.transition(q, r)),
                         ra.guard(q, r) == False)),


]






# Define data

# store something and accept, as long as you give the stored value, accept, otherwise go back to start and reject
data_m1 = [([], False),
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
        ]

# doing three transitions, and accept if the first and third parameters are the same
data_m2 = [
    ([act(1)], True),
    ([act(1), act(2)], False),
    ([act(1), act(2), act(1)], True),
    ([act(1), act(2), act(3)], False),
    ([act(1), act(2), act(1), act(1)], False),
]

# check for unique valuedness
data_m3 = [
    ([], False),
    ([act(1)], False),
    ([act(1), act(1)], False),
    ([act(1), act(2)], False),
    ([act(1), act(1), act(1)], True),
    ([act(1), act(2), act(1)], True),
    ([act(1), act(2), act(2)], True),
    ([act(1), act(2), act(3)], False),
]

data = data_m3


# Add output constraints for data
output_constraints = []
for seq, accept in data:
    node = trie[seq]
    output_constraints.append(ra.output(m.map(node.node)) == accept)


# Add transition constraints for all transitions in trie
transition_constraints = [ra.start == m.map(trie.node)]
value_constraints = []
for n, a, c in trie.transitions():
    transition_constraints.append(z3.If(z3.Exists([r], z3.And(r != fresh, m.val(n.node, r) == a.value)),
                                        z3.ForAll([r], z3.Implies(z3.And(r != fresh, m.val(n.node, r) == a.value),
                                                                  z3.And(ra.transition(m.map(n.node), r) == m.map(c.node),
                                                                         ra.guard(m.map(n.node), r) == True))),
                                        ra.transition(m.map(n.node), fresh) == m.map(c.node)))

    # If we update a non-fresh register on a transition from a state,
    # then the register is assigned the value.
    # Else, the register keeps its previous value.
    transition_constraints.append(z3.ForAll([r, rp],
              z3.Implies(z3.And(ra.transition(m.map(n.node), r) == m.map(c.node),
                                ra.guard(m.map(n.node), r) == True
                                ),
                         z3.If(r != fresh,
                               m.val(c.node, r) == m.val(n.node, r),
                               z3.Implies(ra.update(m.map(n.node), r) == rp,
                                          m.val(c.node, rp) == a.value)))))

    # for all n - v -> c where n.r != c.r -> update r
    transition_constraints.append(z3.ForAll([r, rp],
                                            z3.Implies(z3.And(r != fresh,
                                                              m.val(c.node, r) != m.val(n.node, r),
                                                              ra.transition(m.map(n.node), rp) == m.map(c.node)),
                                                       ra.update(m.map(n.node), rp) == r)))


# Create an empty value and assert that all (neat) values are different
values = {init}
for n, a, c in trie.transitions():
    values.add(a.value)

distinct_values = z3.Distinct(list(values))
print(distinct_values)
s = z3.Solver()
s.add(axioms)
s.add(transition_constraints)
s.add(output_constraints)
s.add(distinct_values)

print(s.check())
model = s.model()
print(model)
print(locations)
for seq, accept in data:
    print(model.eval(ra.output(m.map(trie[seq].node)) == accept))
for n in trie:
    print('{0} maps to {1}'.format(n.node, model.eval(m.map(n.node))))

n = z3.Const('n', Node)
