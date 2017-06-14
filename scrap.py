import collections
import z3

# states
n = 3
State = z3.Datatype('State')
for i in range(n):
    State.declare('state{0}'.format(i))
State = State.create()
state = z3.Const('state', State)

# registers
k = 1
Register = z3.Datatype('Register')
Register.declare('fresh')
for i in range(1, k+1):
    Register.declare('register{0}'.format(i))
Register = Register.create()
registers = [Register.fresh, Register.register1]
register = z3.Const('register', Register)
fresh = Register.fresh

print(registers)

# inputs
Value = z3.DeclareSort('Value')
val = z3.Const('val', Value)
other = z3.Const('other', Value)

RegisterAutomaton = collections.namedtuple('RegisterAutomaton', 'start transition output registers set select store')
ra = RegisterAutomaton(start=z3.Const('start', State),
                       transition=z3.Function('transition', State, Value, State),
                       output=z3.Function('output', State, z3.BoolSort()),
                       registers=registers,
                       set=z3.Function('set', State, Register, z3.BoolSort()),
                       select=z3.Function('select', State, Value, Register),
                       store=z3.Function('store', State, Value, Register))

axioms = [z3.ForAll([register],
                    z3.Implies(register != fresh, ra.set(ra.start, register) == False)),
          z3.ForAll([state, val],
                    z3.And([
                        z3.And(
                        # a (non-fresh) guard on transition implies that it is set in the source
                        z3.Implies(ra.select(state, val) == register,
                                   ra.set(state, register) == True),
                        # an update of a (non-perp) register on a transition implies
                        #  that there is no guard on that register on that transition
                        z3.Implies(ra.store(state, val) == register,
                                   ra.select(state, val) == fresh),
                        # if a register is updated is must be used
                        z3.Implies(ra.store(state, val) == register,
                                   ra.set(ra.transition(state, val), register) == True),
                        # If a variable is used after a transition, then it was either used before the transition,
                        #  or it stores the parameter carried by the transition
                        z3.Implies(ra.set(ra.transition(state, val), register) == True,
                                   z3.Or(ra.set(state, register) == True,
                                         z3.And(ra.select(state, val) == fresh,
                                                ra.store(state, val) == register))))
                        for register in registers[1:]]),
                    patterns = [ra.transition(state, val)]),
          z3.ForAll([state, val, other],
                    z3.Implies(z3.And([val != other, ra.transition(state, val) != ra.transition(state, other)]),
                               ra.select(state, val) != ra.select(state, other)))]


def _state(aut, access):
    if not access:
        return aut.start
    return aut.transition(_state(aut, access[:-1]), access[-1])

def canonical(seq):
    values = {}
    i = 0
    for input in seq:
        if input not in values:
            values[input] = z3.Const('val{0}'.format(i), Value)
            i = i + 1
    return [values[input] for input in seq]


constraints = [ra.output(_state(ra, canonical('11'))) == True,
               ra.output(_state(ra, canonical('10'))) == False,
               ra.output(_state(ra, canonical('110'))) == False,
               ra.output(_state(ra, canonical('111'))) == True,
               ra.output(_state(ra, canonical('11101'))) == True,
               ra.output(_state(ra, canonical('111011'))) == True,

               # bijection
               ra.output(_state(ra, canonical('00'))) == True,
               ra.output(_state(ra, canonical('88555'))) == True,

               z3.Distinct([z3.Const('val{0}'.format(i), Value) for i in range(2)])
               ]

solver = z3.Solver()
solver.add(axioms + constraints)

if solver.check() == z3.sat:
    model = solver.model()
    print(model)
else:
    print(solver.unsat_core())
    print(z3.simplify(z3.And(axioms + constraints)))

