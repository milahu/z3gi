import collections
import z3

# states
n = 2
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
Input = z3.DeclareSort('Input')
input = z3.Const('input', Input)
input2 = z3.Const('input2', Input)

RegisterAutomaton = collections.namedtuple('RegisterAutomaton', 'start transition output registers set select store')
ra = RegisterAutomaton(start=z3.Const('start', State),
                       transition=z3.Function('transition', State, Input, State),
                       output=z3.Function('output', State, z3.BoolSort()),
                       registers=registers,
                       set=z3.Function('set', State, Register, z3.BoolSort()),
                       select=z3.Function('select', State, Input, Register),
                       store=z3.Function('store', State, Input, Register))

axioms = [z3.ForAll([register],
                    z3.Implies(register != fresh, ra.set(ra.start, register) == False)),
          z3.ForAll([state, input],
                    z3.And([
                        z3.And(
                        # a (non-fresh) guard on transition implies that it is set in the source
                        z3.Implies(ra.select(state, input) == register,
                                   ra.set(state, register) == True),
                        # an update of a (non-perp) register on a transition implies
                        #  that there is no guard on that register on that transition
                        z3.Implies(ra.store(state, input) == register,
                                   ra.select(state, input) == fresh),
                        # if a register is updated is must be used
                        z3.Implies(ra.store(state, input) == register,
                                   ra.set(ra.transition(state, input), register) == True),
                        # If a variable is used after a transition, then it was either used before the transition,
                        #  or it stores the parameter carried by the transition
                        z3.Implies(ra.set(ra.transition(state, input), register) == True,
                                   z3.Or(ra.set(state, register) == True,
                                         z3.And(ra.select(state, input) == fresh,
                                                ra.store(state, input) == register))))
                        for register in registers[1:]]),
                    patterns = [ra.transition(state, input)]),
          z3.ForAll([state, input, input2],
                    z3.Implies(z3.And([input != input2, ra.transition(state, input) != ra.transition(state, input2)]),
                               ra.select(state, input) != ra.select(state, input2)))]


def _state(aut, access):
    if not access:
        return aut.start
    return aut.transition(_state(aut, access[:-1]), z3.Const(access[-1], Input))


constraints = [ra.output(_state(ra, '11')) == True,
               ra.output(_state(ra, '10')) == False,
               ra.output(_state(ra, '110')) == False,
               ra.output(_state(ra, '111')) == True,
               ra.output(_state(ra, '11101')) == True,
               ra.output(_state(ra, '111011')) == True,

               # bijection doesn't work
               #ra.output(_state(ra, '00')) == True
               ]

solver = z3.Solver()
solver.add(axioms + constraints)

if solver.check() == z3.sat:
    model = solver.model()
    print(model)
else:
    print(solver.unsat_core())
    print(z3.simplify(z3.And(axioms + constraints)))

