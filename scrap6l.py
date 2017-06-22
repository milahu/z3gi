# WORKING! encoding
import collections

import itertools
import z3

num_locations = 4
num_registers = 2
num_labels = 1
def enum(type, names):
    dt = z3.Datatype(type)
    for name in names:
        dt.declare(name)
    dt = dt.create()
    fields = [dt.__getattribute__(name) for name in names]
    return (dt, fields)

Label, labels = enum('Label', ['label{0}'.format(i) for i in range(num_labels)])
Location, locations = enum('Location', ['location{0}'.format(i) for i in range(num_locations)])
Register, registers = enum('Register', ['register{0}'.format(i) for i in range(num_registers)] + ['fresh'])
fresh = registers[-1]

Value = z3.DeclareSort('Value')
Node = z3.DeclareSort('Node')

def is_fresh(reg):
   return str(reg) == str(fresh)

RegisterAutomaton = collections.namedtuple('RegisterAutomaton',
                                           'start transition output guard update')

def register_automaton(Location, Register, start):
    return RegisterAutomaton(start = start,
                             # For r != fresh, transition(q, l, r) only makes sense if guard(q, l, r) == true.
                             # In this case there is a transition q -- l(v), v==r -> transition(q, l, r),
                             # Otherwise, use q -- l(v), fresh -> transition(q, l, fresh).
                             transition = z3.Function('transition', Location, Label, Register, Location),
                             guard=z3.Function('guard', Location, Label, Register, z3.BoolSort()),
                             update = z3.Function('update', Location, Label, Register),
                             output=z3.Function('output', Location, z3.BoolSort()),
                             )

Mapper = collections.namedtuple('Mapper',
                               'map val')

def mapper(Node, Location, Value, Register):
    return Mapper(map = z3.Function('map', Node, Location),
                  val = z3.Function('valuation', Node, Register, Value))

Action = collections.namedtuple('Action',
                                'label value')

act = lambda x: Action(labels[0], x)

def determinize(seq):
   neat = {}
   i = 0
   for action in seq:
       if action.value not in neat:
           neat[action.value] = z3.Const('val{0}'.format(i), Value)
           i = i + 1
   return [act(neat[action.value]) for action in seq]


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

l = z3.Const('l', Label)
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

   z3.ForAll([q, l],
             ra.guard(q, l, fresh) == True
             ),

   # In the start state of the mapper,
   # all registers contain a value outside the domain of plausible values.
   z3.ForAll([r],
             z3.Implies(r != fresh,
                        m.val(root, r) == init)
             ),

   z3.ForAll([q, l, r],
             z3.Implies(z3.And(r != fresh,
                               ra.transition(q, l, fresh) == ra.transition(q, l, r)),
                        ra.guard(q, l, r) == False)),


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

# check for unique valuedness (non-UV 4 LOC, UV 5 LOC)
data_m3 = [
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
   ([act(1), act(1), act(1), act(2)], True),
   ([act(1), act(1), act(1), act(1), act(2)], True),
   ([act(1), act(1), act(1), act(1), act(2), act(2)], True),
   ([act(1), act(1), act(1), act(2), act(2)], True),
   ([act(1), act(1), act(1), act(2), act(3)], True),
   ([act(1), act(2), act(2), act(2)], True),
   ([act(1), act(2), act(2), act(1)], True),
   ([act(1), act(2), act(3), act(4), act(1)], True),
   ([act(1), act(2), act(2), act(2), act(3)], True),

]

# check for non-shifting property (3 LOC NS, 4 LOC non-NS)
# expect this system to require one additional location than if our constraints allowed value shifting between registers
data_m4 = [
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
   ([act(1), act(2), act(1), act(2), act(1), act(2)], True),
]


data = data_m3
from random import shuffle
shuffle(data)

# Add output constraints for data
output_constraints = []
for seq, accept in data:
   node = trie[seq]
   output_constraints.append(ra.output(m.map(node.node)) == accept)


# Add transition constraints for all transitions in trie
transition_constraints = [ra.start == m.map(trie.node)]
value_constraints = []
for n, a, c in trie.transitions():
    transition_constraints.extend([

        # if a transition is made, it must have been guarded
        z3.ForAll(
            [r],
            z3.Implies(
                ra.transition(m.map(n.node), a.label, r) == m.map(c.node),
                ra.guard(m.map(n.node), a.label, r) == True
            )
        ),

        # if a register has changed, it must have been updated
        z3.ForAll(
            [r],
            z3.Implies(
                z3.And(r != fresh, m.val(c.node, r) != m.val(n.node, r)),
                ra.update(m.map(n.node), a.label) == r
            )
        ),

        # if a register is updated, it must contain the current value
        z3.ForAll(
            [r],
            z3.Implies(
                z3.And(r != fresh, ra.update(m.map(n.node), a.label) == r),
                m.val(c.node, r) == a.value
            )
        ),

        # selecting the right transition
        z3.If(
            z3.Exists(
                [r],
                z3.And(r != fresh, m.val(n.node, r) == a.value)
            ),
            z3.ForAll( # !! Is this still OK? (we don't have unique valuedness)
                [r],
                z3.Implies(
                    z3.And(r != fresh, m.val(n.node, r) == a.value),
                    z3.If(
                        ra.guard(m.map(n.node), a.label, r) == True,
                        ra.transition(m.map(n.node), a.label, r) == m.map(c.node),
                        ra.transition(m.map(n.node), a.label, fresh) == m.map(c.node),
                    )
                )
            ),
            ra.transition(m.map(n.node), a.label, fresh) == m.map(c.node))
    ])


   # If we update a non-fresh register on a transition from a state,
   # then the register is assigned the value.
   # Else, the register keeps its previous value.
   # transition_constraints.append(
   #     z3.ForAll(
   #         [r, rp],
   #         z3.Implies(
   #             z3.And(
   #                 ra.transition(m.map(n.node), a.label, r) == m.map(c.node),
   #                 ra.guard(m.map(n.node), a.label, r) == True
   #             ),
   #             z3.If(
   #                 r != fresh,
   #                 m.val(c.node, r) == m.val(n.node, r),
   #                 z3.Implies(
   #                     ra.update(m.map(n.node), a.label, r) == rp,
   #                     m.val(c.node, rp) == a.value
   #                 )
   #             )
   #         )
   #     )
   # )

   # # for all n - v -> c where n.r != c.r -> update r
   # transition_constraints.append(
   #     z3.ForAll(
   #         [r, rp],
   #         z3.Implies(
   #             z3.And(
   #                 r != fresh,
   #                 m.val(c.node, r) != m.val(n.node, r),
   #                 ra.transition(m.map(n.node), a.label, rp) == m.map(c.node),
   #                 ra.guard(m.map(n.node), a.label, rp) == True
   #             ),
   #             ra.update(m.map(n.node), a.label, rp) == r
   #         )
   #     )
   # )


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
#s2 = z3.Solver()
#all = transition_constraints + output_constraints + output_constraints + [distinct_values]
chk = s.check()
if str(chk) == "unsat":
   print(chk)
   print(s.unsat_core())
   print(s.statistics())
   exit(0)
model = s.model()
print(s.statistics())
print(model)
print(locations)
for seq, accept in data:
   print(model.eval(ra.output(m.map(trie[seq].node)) == accept))
for n in trie:
   print('{0} maps to {1}'.format(n.node, model.eval(m.map(n.node))))

"""
Visitor class for implementing procedures on inferred RAs.
"""
class RaVisitor:
   def __init__(self):
      super().__init__()
   """
   Visits every location and transition in the register automaton.
   """
   def process(self, m, ra, labels, regs, locations):
      to_visit = [ra.start]
      visited = []
      while (len(to_visit) > 0):
         loc = to_visit.pop(0)
         acc = model.eval(ra.output(loc))
         self._visit_location(loc, acc)
         visited.append(loc)
         next_trans  = []
         for l in labels:
            for r in regs:
               guard_enabled = model.eval(ra.guard(loc, l, r))
               if guard_enabled:
                  next_loc = model.eval(ra.transition(loc, l, r))
                  next_asg = model.eval(ra.update(loc, l))
                  next_trans.append((loc, l, r, next_asg, next_loc))

         for (start_loc, label, guard, asg, end_loc) in next_trans:
            self._visit_transition(start_loc, label, guard, asg, end_loc)
            if end_loc not in visited and end_loc not in to_visit:
               to_visit.append(end_loc)
         # we sort according to the location strings so we get them in order
         to_visit.sort(key=lambda loc: str(loc))
   """
   Visits locations in the RA in lexographical order starting from the initial location.
   """
   def _visit_location(self, loc, acc):
      raise NotImplementedError()
   """
   Visits transitions in the RA.
   """
   def _visit_transition(self, start_loc, label, guard, asg, end_loc):
      raise NotImplementedError()
class RaPrinter(RaVisitor):
   def __init__(self):
      super().__init__()
   """
   Prints location.
   """
   def _visit_location(self, loc, acc):
      print("{0}({1})".format(str(loc), "+" if acc == True else "-") )
   """
   Prints transition.
   """
   def _visit_transition(self, start_loc, label, guard, asg, end_loc):
      print("\t{0} -> {1}({2}) {3} {4}".format(str(start_loc), str(label), str(guard), str(asg), str(end_loc)))
# TODO it should probably store locations/regs as strings
class SimpleRa():
   def __init__(self, locations, loc_to_acc, loc_to_trans, registers):
      super().__init__()
      self.locations = locations
      self.loc_to_acc = loc_to_acc
      self.loc_to_trans = loc_to_trans
      self.register = registers
   def get_start_loc(self):
      return self.locations[0]
   def get_locations(self):
      return list(self.locations)
   def get_transitions(self, loc, label=None):
      if label is None:
         return list(self.loc_to_trans[loc])
      else:
         return list([trans for trans in self.loc_to_trans[loc] if trans[1] == label])
   def get_registers(self):
      return list(registers)
   def get_acc(self, loc):
      return self.loc_to_acc[loc]
class NoTransitionTriggeredException(Exception):
   pass
class SimpleRaSimulator():
   def __init__(self, sra):
      super().__init__()
      self.ra = sra
   """
   Runs the given sequence of values on the RA.
   """
   def accepts(self, trace):
      init = -1
      reg_val =  dict()
      for reg in self.ra.get_registers():
         reg_val[reg] = init
      loc = self.ra.get_start_loc()
      for act in trace:
         next_transitions = self.ra.get_transitions(loc, act.label)
         # to define a fresh guard we need to know which register guards are present
         active_regs = [trans[2] for trans in next_transitions]
         n_loc = None
         for (_, _, guard, asg, next_loc) in next_transitions:
            if (self._is_satisfied(act, guard, active_regs, reg_val)):
               if not is_fresh(asg):
                  reg_val[asg] = act.value
               n_loc = next_loc
               break
         if n_loc is None:
            print("In location {0} with trans. {1}, \n reg vals {2} and crt val {3}".format(
               str(loc), str(next_transitions), str(reg_val), str(act.value)
            ))
            raise NoTransitionTriggeredException()
         else:
            loc = n_loc
      return self.ra.get_acc(loc)
   def _is_satisfied(self, act, guard, active_regs, reg_val):
      if is_fresh(guard):
         reg_vals = list([reg_val[reg] for reg in active_regs])
         return act.value not in reg_vals
      else:
         return act.value is reg_val[guard]
"""
Builds a SRA from the inferred uninterpreted functions for the RA.
"""
class SimpleRaBuilder(RaVisitor):
   def __init__(self):
      super().__init__()
      self.locations = []
      self.loc_to_acc = dict()
      self.loc_to_trans = dict()
      self.registers = []
   def _visit_location(self, loc, acc):
      self.locations.append(loc)
      self.loc_to_acc[loc] = acc
      if loc not in self.loc_to_trans:
         self.loc_to_trans[loc] = []
   def _visit_transition(self, start_loc, label, guard, asg, end_loc):
      self.loc_to_trans[start_loc].append((start_loc, label, guard, asg, end_loc))
      if not is_fresh(guard) and guard not in self.registers:
         print("guard",guard)
         self.registers.append(guard)
      if not is_fresh(asg) and asg not in self.registers:
         print("asg", asg, asg is not fresh)
         self.registers.append(asg)
   """
   Builds a SRA from the RA generated functions. It uses as locations and registers the actual Z3 constants.
   """
   def build_ra(self):
      return SimpleRa(self.locations, self.loc_to_acc, self.loc_to_trans, self.registers.sort(key=lambda reg: str(reg)))
"""
Checks if a sra corresponds to a given sequence of acc/rej observations.
Returns a 4-tuple with the first element True (if conforming), or False (if not).
For the False case, the next elements provide the trace, observed acceptance and sra acceptance.
"""
def conforms_to_obs(sra, obs):
   runner = SimpleRaSimulator(sra)
   for (actions, acc) in obs:
      trace = actions
      ra_acc = runner.accepts(trace)
      if str(ra_acc) is not str(acc):
         return (False, trace, acc, ra_acc)
   return (True, None, None, None)
printer = RaPrinter()
printer.process(model, ra, labels, registers, locations)
builder = SimpleRaBuilder()
builder.process(model, ra, labels, registers, locations)
sra = builder.build_ra()
conforms = conforms_to_obs(sra, data)
print(conforms)
#runner = SimpleRaSimulator(sra)
#print(runner.accepts([0, 1, 1]))
#print(runner.accepts([0, 1, 0, 1]))
#print(runner.accepts([0, 1, 0, 1, 0, 1]))
#n = z3.Const('n', Node)
