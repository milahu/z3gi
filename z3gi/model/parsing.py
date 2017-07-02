import sys
from xml.etree import ElementTree

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


def xml_to_iora (file_name:str):
    """Takes a .xml register automata and produces a iora"""
    xmlrootelem = ElementTree.ElementTree(file=file_name).getroot()

    # see doc at : http://docs.python.org/2/library/xml.etree.elementtree.html

    # print getPrettyPrintedString(xmlrootnode)

    #          <symbol name="OFrame">
    #             <param type="int" name="p0"/>
    #             <param type="int" name="p1"/>
    #          </symbol>
    def get_labels(xmlElem):
        symbols = []
        if not xmlElem:
            return []
        for symbol in xmlElem:
            #params = []
            #for param in symbol:
            #    params += [(param.attrib["type"], param.attrib["name"])]
                # note parameter names not important for symbol type declaration in alphabet
            #symbols += [symbol.attrib["name"], params)]
            symbols += symbol.attrib["name"]
        return symbols

    elemAlphabet = xmlrootelem.find("alphabet")
    inputs = get_labels(elemAlphabet.find("inputs"))
    outputs = get_labels(elemAlphabet.find("outputs"))

    symbolname2params = {}
    for symbol in inputs + outputs:
        symbolname2params[symbol.getName()] = symbol.getParamNames()

    initLocation = None
    locations = []
    id2location = {}
    for locationxml in xmlrootelem.iter("location"):
        name = locationxml.attrib["name"]

        if locationxml.attrib.has_key("initial") and locationxml.attrib["initial"] == "true":
            location = Location(name, initial=True)
            initLocation = location
        else:
            location = Location(name, initial=False)
        # print location.to_xml()
        locations += [location]
        id2location[location.getId()] = location

    transitions = []
    for transitionxml in xmlrootelem.iter("transition"):
        tr_from = transitionxml.attrib["from"]
        tr_to = transitionxml.attrib["to"]
        tr_symbol = transitionxml.attrib["symbol"]
        tr_param_names = []
        if transitionxml.attrib.has_key("params"):
            paramsstr = transitionxml.attrib["params"]
            tr_param_names = [param.strip() for param in paramsstr.split(',')]
        else:
            # default param names from alphabet definition
            if symbolname2params.has_key(tr_symbol):
                tr_param_names = symbolname2params[tr_symbol]
        guardElem = transitionxml.find("guard")
        tr_guard = ""
        if guardElem is not None:
            tr_guard = guardElem.text
        assigns = []
        for assignxml in transitionxml.iter("assign"):
            assign_to = assignxml.attrib["to"]
            assign_value = assignxml.text
            assigns += [assign_to + "=" + assign_value]

        transition = Transition(
            id2location[tr_from],
            id2location[tr_to],
            tr_symbol,
            tr_param_names,
            tr_guard,
            assigns
        )
        transitions += [transition]

    constants = []
    constantsElem = xmlrootelem.find("constants")
    if constantsElem is not None:
        for constantxml in constantsElem:
            c_type = constantxml.attrib["type"]
            c_name = constantxml.attrib["name"]
            c_value = constantxml.text
            constants += [Constant(c_name, c_value, c_type)]

    globalVars = []
    globalsElem = xmlrootelem.find("globals")
    if globalsElem is not None:
        for globalxml in globalsElem:
            c_type = globalxml.attrib["type"]
            c_name = globalxml.attrib["name"]
            c_value = globalxml.text
            globalVars += [GlobalVar(c_name, c_value, c_type)]

    reg = Register(alphabet, constants, globalVars, locations, transitions, initLocation)
    return reg

