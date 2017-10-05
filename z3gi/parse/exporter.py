import sys

from model import Automaton, Acceptor, Transition
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

def to_dot (automaton:Automaton, write_to_file:str=None) -> str:
    """For an automaton produces a .dot representation"""
    dot = ""
    dot += 'digraph g {\n'
    for state in automaton.states():
        dot += '\t{};\n'.format(w_state(automaton,state))

    for state in automaton.states():
        for trans in automaton.transitions(state):
            dot += "\t{};\n".format(w_trans(automaton, trans))

    dot+='}'

    if write_to_file is not None:
        f = open(write_to_file, 'w')
        f.write(dot)
        f.close()
    return dot