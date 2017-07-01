import sys

from model import *
from model.fa import IOTransition
from model.ra import RATransition, IORATransition

__all__ = [
           "to_dot",
          ]

sep = "_"

def w_state(automaton : Automaton, state):
    if isinstance(automaton, Acceptor):
        return sep.join(state, str(automaton.is_accepting(state)))
    return state

def w_trans(automaton:Automaton, trans : Transition):
    input_elements = [str(trans.start_label)]
    if isinstance(trans, RATransition):
        input_elements.extend([str(trans.guard), str(trans.assignment)])
    input_label = sep.join(input_elements)

    output_elements = []
    if isinstance(automaton, Acceptor):
        output_elements.append(str(automaton.is_accepting(trans.end_state)))
    elif isinstance(trans, IOTransition):
        output_elements.append(trans.output)
    elif isinstance(trans, IORATransition):
        output_elements.extend(
            map(lambda x:str(x), [trans.output_label, trans.output_mapping, trans.output_assignment]))
    output_label = sep.join(output_elements)
    return '{0} -> {1} [label="{2}/{3}"]'.format( w_state(automaton, trans.start_state),
                                                   w_state(automaton, trans.end_state),
                                                   input_label,
                                                   output_label)

def to_dot (automaton:Automaton, file_name:str):
    """For an automaton produces a .dot representation"""
    f = open(file_name, 'w') if file_name is not None else sys.stdout
    print('digraph g {\n', file=f)
    for state in automaton.states():
        print('\t%s;' % w_state(automaton,state), file=f)

    for state in automaton.states():
        for trans in automaton.transitions(state):
            print("\t%s;" % w_trans(automaton, trans), file=f)

    print('}', file=f)

    if file_name is not None:
        f.close()




