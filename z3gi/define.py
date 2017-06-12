import collections
import z3

STATE = z3.DeclareSort('STATE')
INPUT = z3.DeclareSort('INPUT')
OUTPUT = z3.DeclareSort('OUTPUT')
ELEMENT = z3.DeclareSort('ELEMENT')

FSM = collections.namedtuple('FSM', 'start transition output')


def DFA(name=''):
    if name:
        name = name + '_'
    return FSM(start=z3.Const('{0}start'.format(name), STATE),
               transition=z3.Function('{0}transition'.format(name), STATE, INPUT, STATE),
               output=z3.Function('{0}output'.format(name), STATE, z3.BoolSort()))


def MooreMachine(name=''):
    if name:
        name = name + '_'
    return FSM(start=z3.Const('{0}start'.format(name), STATE),
               transition=z3.Function('{0}transition'.format(name), STATE, INPUT, STATE),
               output=z3.Function('{0}output'.format(name), STATE, OUTPUT))


def MealyMachine(name=''):
    if name:
        name = name + '_'
    return FSM(start=z3.Const('{0}start'.format(name), STATE),
               transition=z3.Function('{0}transition'.format(name), STATE, INPUT, STATE),
               output=z3.Function('{0}output'.format(name), STATE, INPUT, OUTPUT))


def StateMapper(name=''):
    if name:
        name = name + '_'
    return z3.Function('{0}statemap'.format(name), ELEMENT, STATE)


def state(name='state'):
    return z3.Const(str(name), STATE)


def input(name='input'):
    return z3.Const(str(name), INPUT)


def output(name='output'):
    return z3.Const(str(name), OUTPUT)


def element(name='element'):
    return z3.Const(str(name), ELEMENT)


def domain(f):
    return tuple(f.domain(i) for i in range(f.arity()))
