from abc import ABCMeta, abstractmethod
from typing import Type, Dict, List, Union

import sys
import inspect
import re

from model import Automaton, Acceptor, Transition
from model.fa import IOTransition, MutableMealyMachine
from model.ra import RATransition, IORATransition, Action

__all__ = [

    "extract_traces_from_file",
    "build_automaton_from_dot"
          ]


def extract_traces_from_file(file_name:str, aut_type:Type[Union[Automaton,str]]) -> List[object]:
    """Parses file with traces that is formatted in an adapted Abbadingo format, and returns an accepting/rejecting or an
    input/output trace (depending on the line's format).
    The format of the file is:
    trace1
    trace2
    ...

    Depending on the formalism(aut_type), the format of a trace is one of the following:
    acc_value[ label]*
    acc_value[ label(?value)]
    input/output[ input/output]*
    input(?value)/output(?value)[ input(?value)/output(?value)]*
    """

    line_stream = file_stream(file_name)
    if isinstance(aut_type, Automaton):
        formalism = aut_type.__name__
    else:
        formalism = aut_type
    formalism=formalism.replace("RegisterAutomaton", "RA")
    crt = sys.modules[__name__]
    parse_fun = crt.__dict__[formalism+"_parse"]
    if parse_fun is None:
        sup_form = [a.replace("_parse","") for a in crt.__dict__.keys() if a.endswith("parse") and isinstance(crt.__dict__[a], function)]
        print("Formalism not supported")
        print("Supported formalisms: ", sup_form)
        exit(0)
    traces = [parse_fun(line) for line in line_stream]
    return traces

def act_string_to_act(act_string):
    act_label = act_string[:act_string.index("(")]
    param_val = int(act_string[act_string.index("(") + 1:act_string.index(")")]) \
        if act_string.index(")") > act_string.index("(") + 1 else None
    return Action(act_label, param_val)

def DFA_parse(line):
    fields = line.split()
    acc = bool(int(fields[0]))
    labels = fields[1:]
    return (labels, acc)

def RA_parse(line):
    fields = line.split()
    acc = bool(int(fields[0]))
    act_strings = fields[1:]
    actions = list(map(act_string_to_act, act_strings))
    return actions

def MealyMachine_parse(line):
    fields = line.split()
    trace = []
    for field in fields:
        split = field.split('/')
        trace.append((split[0], split[1]))
    return trace

def IORA_parse(line):
    fields = line.split()
    trace = []
    for field in fields:
        split = field.split('/')
        trace.append((act_string_to_act(split[0]), act_string_to_act(split[1])))
    return trace

def build_automaton_from_dot (aut_type:str, file_name:str) -> Automaton:
    """
    Builds an automaton from a .dot model
    :param aut_type: the type of automaton described in the .dot file
    :param file_name: path/name of the .dot file
    :return: The constructed automaton or None
    """
    crt = sys.modules[__name__]
    importer_cls = getattr(crt, aut_type + "DotImporter")
    if importer_cls is None:
        print("DotImporter not available for automaton ", aut_type)
        print("Available DotImporters: ",
              [a.replace("DotImporter","") for a in crt.__dict__.keys() if a.endswith("DotImporter") and isinstance(crt.__dict__[a], type)
               and not inspect.isabstract(crt.__dict__[a])])
        exit(1)

    """From .dot representation produces an automata"""
    dot_stream = file_stream(file_name)
    importer = importer_cls()
    importer.parse_dot(dot_stream)
    automata = importer.build_aut()
    return automata

def file_stream(file_name, from_line=0, line_processor=None):
    f = open(file_name, 'r')
    _ = [f.readline() for i in range(from_line)]
    for line in f:
        yield line if line_processor is None else line_processor(line)
    f.close()


# a simple dot parser using REGEX, in particular, we use labelled capturing groups
# e.g. (?<allones>1*) captures the regex 1*. In case of a capture (or match), the matching string will be stored
# in a group indexed by "allones"
# note, this parser ABSOLUTELY does not implement thorough grammar checks
class DotImporter(metaclass=ABCMeta):
    # some patterns
    PAT_NO_NEWLINE = "[^(\r\n|[\r\n])]"
    PAT_NEWLINE = "(\r\n|[\r\n])"
    PAT_STATE = "s[0-9]*"
    PAT_STATE_STR = "(?P<state>"+PAT_STATE+")" + "(?P<content>[^>\[]*)"+"(\[.*\])?;?"
    PAT_TRANS_LABEL = "\[label=\"(?P<label>.*)\"\];?"
    PAT_TRANS_MOVE = "(?P<src>" + PAT_STATE + ")\s*->\s*" + "(?P<dst>"+  PAT_STATE + ")"
    PAT_TRANSITION = PAT_TRANS_MOVE+ "\s*" + PAT_TRANS_LABEL

    PAT_START = "digraph.*"
    PAT_ENDS_ON_LABEL = "(?= " + PAT_TRANS_LABEL + ")"

    @abstractmethod
    def _visit_state(self, state_str:str, state_content:str):
        pass

    @abstractmethod
    def _visit_transition(self, from_state:str, to_state:str, trans_label:str):
        pass

    @abstractmethod
    def build_aut(self):
        pass

    def _matching_lines(self, stream, pat, expected=True, stop_at_mismatch=True):
        matches = []
        for line in stream:
            line = line.strip()
            print(line)
            # if the line only contained spaces continue
            if len(line) == 0:
                continue
            match = re.fullmatch(pat, line)
            if match is not None:
                matches.append(match)
            else:
                if stop_at_mismatch is True:
                    break

        if len(matches) == 0:
            print("Wrong format, cannot find match for ",pat)
            print("Expected format (empty lines/whitespaces ignored): \n"+
                self.PAT_START+"\n" +
                self.PAT_STATE_STR+"\n" +
                "..." +
                self.PAT_TRANSITION +
                "...")
            exit(1)

        return matches

    def parse_dot(self, line_stream:str):
        patterns = dict()
        _ = self._matching_lines(line_stream, self.PAT_START, patterns)
        state_matches = self._matching_lines(line_stream, self.PAT_STATE_STR, patterns)
        for state_match in state_matches:
            self._visit_state(state_match.group("state"), state_match.group("content"))

        trans_matches = self._matching_lines(line_stream, self.PAT_TRANSITION, patterns, stop_at_mismatch=False)
        for trans_match in trans_matches:
            self._visit_transition(trans_match.group("src"), trans_match.group("dst"), trans_match.group("label"))

class TransducerDotImporter(DotImporter, metaclass=ABCMeta):
    PAT_IOTRANSITION = "(?P<input>[^/]*)/(?P<output>.*)"

    @abstractmethod
    def _visit_iotransition(self, from_state:str, to_state:str, input_label:str, output_label):
        pass

    def _visit_transition(self, from_state:str, to_state:str, trans_label:str):
        match = re.match(self.PAT_IOTRANSITION, trans_label)
        if match is None:
            print("Invalid transition label " + trans_label)
            print("Expected transition label pattern " + self.PAT_IOTRANSITION)
            exit(1)
        inp_label = match.group("input")
        out_label = match.group("output")
        self._visit_iotransition(from_state, to_state, inp_label, out_label)

class MealyMachineDotImporter(TransducerDotImporter):
    def __init__(self):
        super().__init__()
        self._mut_mealy = MutableMealyMachine()

    def _visit_state(self, state_str:str, state_content:str):
        self._mut_mealy.add_state(state_str)

    def _visit_iotransition(self, from_state:str, to_state:str, input_label:str, output_label):
        self._mut_mealy.add_transition(from_state, IOTransition(from_state, input_label, output_label, to_state))

    def build_aut(self):
        return self._mut_mealy.to_immutable()
