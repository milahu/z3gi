import collections
import z3

State = z3.DeclareSort('State')
Input = z3.DeclareSort('Input')
Output = z3.DeclareSort('Output')
Element = z3.DeclareSort('Element')

Automaton = collections.namedtuple('Automaton', 'start transition output')
RegisterAutomaton = collections.namedtuple('RegisterAutomaton', 'start transition output registers set select store')

def DFA(name=''):
    if name:
        name = name + '_'
    return Automaton(start=z3.Const('{0}start'.format(name), State),
                     transition=z3.Function('{0}transition'.format(name), State, Input, State),
                     output=z3.Function('{0}output'.format(name), State, z3.BoolSort()))


def MooreMachine(name=''):
    if name:
        name = name + '_'
    return Automaton(start=z3.Const('{0}start'.format(name), State),
                     transition=z3.Function('{0}transition'.format(name), State, Input, State),
                     output=z3.Function('{0}output'.format(name), State, Output))


def MealyMachine(name=''):
    if name:
        name = name + '_'
    return Automaton(start=z3.Const('{0}start'.format(name), State),
                     transition=z3.Function('{0}transition'.format(name), State, Input, State),
                     output=z3.Function('{0}output'.format(name), State, Input, Output))

def RegisterDFA(name='', registers=1):
    if name:
        name = name + '_'

    Register = z3.Datatype('{0}Register'.format(name))
    registers = [Register.declare('fresh/perp')]
    for i in range(1, registers+1):
        registers.append(Register.declare('register{0}'.format(i)))
    Register.create()

    return RegisterAutomaton(start=z3.Const('{0}start'.format(name), State),
                             transition=z3.Function('{0}transition'.format(name), State, Register, State),
                             output=z3.Function('{0}output'.format(name), State, z3.BoolSort()),
                             registers=registers,
                             set=z3.Function('{0}set'.format(name), State, Register, z3.BoolSort()),
                             select=z3.Function('{0}select'.format(name), State, Input, Register),
                             store=z3.Function('{0}store'.format(name), State, Input, Register))


def StateMapper(name=''):
    if name:
        name = name + '_'
    return z3.Function('{0}statemap'.format(name), Element, State)


def state(name='state'):
    return z3.Const(str(name), State)


def input(name='input'):
    return z3.Const(str(name), Input)


def output(name='output'):
    return z3.Const(str(name), Output)


def element(name='element'):
    return z3.Const(str(name), Element)


def domain(f):
    return tuple(f.domain(i) for i in range(f.arity()))
