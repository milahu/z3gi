import collections
from abc import ABCMeta, abstractmethod

import z3
from define import enum, Automaton
import model.fa


def FSM(Automaton,metaclass=ABCMeta):
    @abstractmethod
    def __init__(self, num_states):
        self.State, self.states = enum('State', ['state{0}'.format(i) for i in range(num_states)])

def DFA(FSM):
    def __init__(self, labels, num_states):
        super.__init__(num_states)
        self.Label, elements = enum('Label', labels)
        self.labels = {labels[i]: elements[i] for i in range(len(labels))}
        self.transition = z3.Function('transition', self.State, self.Label, self.State)
        self.output = z3.Function('output', self.State, z3.BoolSort())

    def export(self, model : z3.ModelRef) -> model.fa.DFA:
        pass
        #builder = DFABuilder(self)
        #dfa = builder.build_dfa(self)
        #return dfa


def MealyMachine(FSM):
    def __init__(self, input_labels, output_labels, num_states):
        super.__init__(num_states)
        self.Input, elements = enum('Input', input_labels)
        self.inputs = {input_labels[i]: elements[i] for i in range(len(input_labels))}
        self.Output, elements = enum('Output', output_labels)
        self.outputs = {output_labels[i]: elements[i] for i in range(len(output_labels))}
        self.transition = z3.Function('transition', self.State, self.Input, self.State)
        self.output = z3.Function('output', self.State, self.Input, self.Output)

    def export(self, model : z3.ModelRef) -> model.fa.MealyMachine:
        builder = MealyMachineBuilder(self)
        mealy = builder.build_mealy(model)
        return mealy


class MealyMachineBuilder(object):
    def __init__(self, mm : MealyMachine):
        super().__init__()
        self.mm = mm

    def build_mealy(self, model : z3.ModelRef) -> model.fa.MealyMachine:
        tr = FATranslator()
        mut_mm = MutableMealyMachine()


    def _add_state(self, model, translator, mut_ra, z3state):
        z3acc = model.eval(model.eval(self.ra.output(z3state)))
        mut_ra.add_state(translator.z3_to_state(z3state), translator.z3_to_bool(z3acc) )

    def _add_transitions(self, model, translator, mut_ra, z3state, z3label):
        z3end_state_to_guards = dict()
        enabled_z3guards = [guard for guard in self.ra.registers if
                            translator.z3_to_bool(model.eval(self.ra.used(z3state, guard))) or
                            guard is self.ra.fresh
                            ]
        if self.ra.fresh not in enabled_z3guards:
            enabled_z3guards.append(self.ra.fresh)
        for z3guard in enabled_z3guards:
            z3end_state = model.eval(self.ra.transition(z3state, z3label, z3guard))
            if z3end_state not in z3end_state_to_guards:
                z3end_state_to_guards[z3end_state] = []
            z3end_state_to_guards[z3end_state].append(z3guard)
        update = model.eval(self.ra.update(z3state, z3label))
        used_z3regs = [reg for reg in enabled_z3guards if reg is not self.ra.fresh]

        for (z3end_state, z3guards) in z3end_state_to_guards.items():
            # a transition which makes an assignment is never merged
            if self.ra.fresh in z3guards and not translator.z3_to_bool(model.eval(update == self.ra.fresh)):
                self._add_transition(translator, mut_ra, z3state, z3label,
                                     [self.ra.fresh], update, z3end_state, used_z3regs)
                z3guards.remove(self.ra.fresh)
            if len(z3guards) > 0:
                self._add_transition(translator, mut_ra, z3state, z3label,
                                     z3guards, None, z3end_state, used_z3regs)

    def _add_transition(self, translator, mut_ra, z3start_state, z3label, z3guards, z3update, z3end_state, used_z3regs):
        transition = RATransition(translator.z3_to_state(z3start_state), # start state
                                  translator.z3_to_label(z3label), # label
                                  translator.z3_to_guard(z3guards, used_z3regs), # guard
                                  translator.z3_to_assignment(z3update), # assignment
                                  translator.z3_to_state(z3end_state) # end state
                                  )
        mut_ra.add_transition(translator.z3_to_state(z3start_state),transition)
    pass


class FATranslator(object):
    """Provides translation from z3 constants to RA elements. """
    def __init__(self, fa:FSM ):
        self.fa = fa

    def z3_to_bool(self, z3bool):
        return str(z3bool) == "True"

    def z3_to_state(self, z3state):
        return "q"+str(self.fa.states.index(z3state))

    def z3_to_label(self, z3label):
        return str(z3label)
