from abc import ABCMeta, abstractmethod

import z3
import model.fa
from define import Automaton, dt_enum
from model import Transition


class FSM(Automaton,metaclass=ABCMeta):
    @abstractmethod
    def __init__(self, num_states, state_enum=dt_enum):
        self.State, self.states = state_enum('State', ['state{0}'.format(i) for i in range(num_states)])
        self.start = self.states[0]

class DFA(FSM):
    def __init__(self, labels, num_states):
        super().__init__(num_states)
        labels = list(labels)
        self.Label, elements = dt_enum('Label', labels)
        self.labels = {labels[i]: elements[i] for i in range(len(labels))}
        self.transition = z3.Function('transition', self.State, self.Label, self.State)
        self.output = z3.Function('output', self.State, z3.BoolSort())

    def export(self, model : z3.ModelRef) -> model.fa.DFA:
        builder = DFABuilder(self)
        dfa = builder.build_dfa(model)
        return dfa


class MealyMachine(FSM):
    def __init__(self, input_labels, output_labels, num_states, state_enum=dt_enum, label_enum=dt_enum):
        super().__init__(num_states, state_enum=state_enum)
        self.Input, elements = label_enum('Input', input_labels)
        self.inputs = {input_labels[i]: elements[i] for i in range(len(input_labels))}
        self.Output, elements = label_enum('Output', output_labels)
        self.outputs = {output_labels[i]: elements[i] for i in range(len(output_labels))}
        self.transition = z3.Function('transition', self.State, self.Input, self.State)
        self.output = z3.Function('output', self.State, self.Input, self.Output)

    def export(self, model : z3.ModelRef) -> model.fa.MealyMachine:
        builder = MealyMachineBuilder(self)
        mealy = builder.build_mealy(model)
        return mealy

class Mapper(object):
    def __init__(self, fa):
        self.Element = z3.DeclareSort('Element')
        self.start = self.element(0)
        self.map = z3.Function('map', self.Element, fa.State)

    def element(self, name):
        return z3.Const("n"+str(name), self.Element)



class MealyMachineBuilder(object):
    def __init__(self, mm : MealyMachine):
        super().__init__()
        self.mm = mm

    def build_mealy(self, m : z3.ModelRef) -> model.fa.MealyMachine:
        tr = MealyTranslator(m, self.mm)
        mut_mm =  model.fa.MutableMealyMachine()
        for state in self.mm.states:
            mut_mm.add_state(tr.z3_to_state(state))
        for state in self.mm.states:
            for inp in self.mm.inputs.values():
                output = m.eval(self.mm.output(state, inp))
                to_state = m.eval(self.mm.transition(state, inp))
                trans = model.fa.IOTransition(
                    tr.z3_to_state(state),
                    tr.z3_to_input(inp),
                    tr.z3_to_output(output),
                    tr.z3_to_state(to_state))
                mut_mm.add_transition(tr.z3_to_state(state), trans)
        mut_mm.generate_acc_seq()
        return mut_mm.to_immutable()

class DFABuilder(object):
    def __init__(self, dfa : DFA):
        super().__init__()
        self.dfa = dfa

    def build_dfa(self, m : z3.ModelRef) -> model.fa.DFA:
        tr = FATranslator(self.dfa)
        mut_dfa =  model.fa.MutableDFA()
        for state in self.dfa.states:
            accepting = m.eval(self.dfa.output(state))
            mut_dfa.add_state(tr.z3_to_state(state), tr.z3_to_bool(accepting))
        for state in self.dfa.states:
            for labels in self.dfa.labels.values():
                to_state = m.eval(self.dfa.transition(state, labels))
                trans = Transition(
                    tr.z3_to_state(state),
                    tr.z3_to_label(labels),
                    tr.z3_to_state(to_state))
                mut_dfa.add_transition(tr.z3_to_state(state), trans)
        mut_dfa.generate_acc_seq()
        return mut_dfa.to_immutable()

class MealyTranslator(object):
    """Provides translation from z3 constants to RA elements. """
    def __init__(self, model, mm: MealyMachine):
        self._model = model
        self._mm = mm
        self._z3_to_inp = dict(map(reversed, mm.inputs.items()))
        self._z3_to_out = dict(map(reversed, mm.outputs.items()))


    def z3_to_state(self, z3state):
        if z3state in self._mm.states:
            return "q" + str(self._mm.states.index(z3state))
        else:
            return "q" + str(list(map(self._model.eval, self._mm.states)).index(z3state))

    def z3_to_input(self, z3label):
        if z3label in self._z3_to_inp:
            return self._z3_to_inp[z3label]
        else:
            for inp in self._z3_to_inp:
                if self._model.eval(inp) == self._model.eval(z3label):
                    return self._z3_to_inp[inp]

    def z3_to_output(self, z3label):
        if z3label in self._z3_to_out:
            return self._z3_to_out[z3label]
        else:
            for out in self._z3_to_out:
                if self._model.eval(out) == self._model.eval(z3label):
                    return self._z3_to_out[out]

class FATranslator(object):
    """Provides translation from z3 constants to RA elements. """
    def __init__(self, fa:FSM):
        self.fa = fa


    def z3_to_bool(self, z3bool):
        return str(z3bool) == "True"

    def z3_to_state(self, z3state):
        return "q"+str(self.fa.states.index(z3state))

    def z3_to_label(self, z3label):
        return str(z3label)
