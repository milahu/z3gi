import collections
import z3

State = z3.DeclareSort('State')
Input = z3.DeclareSort('Input')
Output = z3.DeclareSort('Output')
Element = z3.DeclareSort('Element')

FSM = collections.namedtuple('FSM', 'start transition output')


def DFA(name=''):
    if name:
        name = name + '_'
    return FSM(start=z3.Const('{0}start'.format(name), State),
               transition=z3.Function('{0}transition'.format(name), State, Input, State),
               output=z3.Function('{0}output'.format(name), State, z3.BoolSort()))


def MooreMachine(name=''):
    if name:
        name = name + '_'
    return FSM(start=z3.Const('{0}start'.format(name), State),
               transition=z3.Function('{0}transition'.format(name), State, Input, State),
               output=z3.Function('{0}output'.format(name), State, Output))


def MealyMachine(name=''):
    if name:
        name = name + '_'
    return FSM(start=z3.Const('{0}start'.format(name), State),
               transition=z3.Function('{0}transition'.format(name), State, Input, State),
               output=z3.Function('{0}output'.format(name), State, Input, Output))


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
