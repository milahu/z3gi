from collections import namedtuple

import z3
from z3gi.model.ra import *
from abc import ABCMeta, abstractmethod


from z3gi.define import Automaton

class RegisterAutomaton(Automaton):

    def __init__(self, labels, num_locations, num_registers):
        self.Label, elements = enum('Label', labels)
        self.labels = {labels[i]: elements[i] for i in range(len(labels))}
        self.Location, self.locations = enum('Location', ['location{0}'.format(i) for i in range(num_locations)])
        self.Register, self.registers = enum('Register', ['register{0}'.format(i) for i in range(num_registers)] + ['fresh'])
        self.start = self.locations[0]
        self.fresh = self.registers[-1]
        self.transition = z3.Function('transition', self.Location, self.Label, self.Register, self.Location)
        self.output = z3.Function('output', self.Location, z3.BoolSort())
        self.used = z3.Function('used', self.Location, self.Register, z3.BoolSort())
        self.guard = z3.Function('guard', self.Location, self.Label, self.Register, z3.BoolSort())
        self.update = z3.Function('update', self.Location, self.Label, self.Register)

    def export(self, model):
        builder = RegisterAutomatonBuilder(self)
        ra = builder.build_ra(model, self.locations, self.labels, self.registers)
        return ra


def enum(name, elements):
    d = z3.Datatype(name)
    for element in elements:
        d.declare(element)
    d = d.create()
    return d, [d.__getattribute__(element) for element in elements]


class RegisterAutomatonBuilder():
    """
    Builder class that construct a register automaton out of a model definition.
    """
    def __init__(self, ra):
        super().__init__()
        self.ra = ra


    def build_ra(self, model, states, labels, regs):
        mut_ra = MutableRegisterAutomaton()
        translator = Translator(self.ra)
        self._add_states(model, translator, mut_ra, states, labels, regs)
        self._add_transitions(model, translator, mut_ra, states, labels, regs)
        return mut_ra.to_immutable()

    def _add_states(self, model, translator, mut_ra, z3states):
        for z3state in z3states:
            z3acc = model.eval(model.eval(self.ra.output(z3state)))
            mut_ra.add_state(translator.z3_to_state(z3state), translator.z3_to_acc(z3acc) )

    def _add_transitions(self, model, translator, mut_ra, z3state, z3label, z3regs):
        registers_used = []
        next_trans = []
        z3end_state_to_guards = dict()
        enabled_z3guards = [guard for guard in z3regs if
                          model.eval(self.ra.guard(z3state, z3label, guard))]
        for z3guard in enabled_z3guards:
            z3end_state = model.eval(self.ra.transition(z3state, z3label, z3guard))
            if z3end_state not in z3end_state_to_guards:
                z3end_state_to_guards[z3end_state] = []
            z3end_state_to_guards[z3end_state].append(z3guard)

        update = model.eval(self.ra.update(z3state, z3label))
        start_state = translator.z3_to_state(z3state)

        for (z3end_state, z3guards) in z3end_state_to_guards.items():
            guard = translator.z3_to_guard(z3guards)
            z3asg = update if self.ra.fresh in z3guards else None
            asg = translator.z3_to_assignment(z3asg)
            end_state = translator.z3_to_state(z3end_state)
            transition = RATransition(start_state, translator.z3_to_label(z3label),
                                      guard, asg, end_state)
            mut_ra.add_transition(start_state, transition)


class Translator():
    """Provides translation from z3 constants to RA elements. """
    def __init__(self, ra):
        super.__init__()
        self.reg_context = dict()
        self.ra = ra

    def z3_to_assignment(self, z3asg):
        if z3asg is None:
            asg = NoAssignment()
        else:
            asg = RegisterAssignment(self.z3_to_register(z3asg))
        return asg

    def z3_to_guard(self, z3guards):
        guard_regs = [self.z3_to_register(z3reg) for z3reg in z3guards if z3reg is not self.ra.fresh]
        if self.ra.fresh in z3guards:
            return FreshGuard(guard_regs)
        else:
            equ_guards = [EqualityGuard(guard_reg) for guard_reg in guard_regs]
            if len(equ_guards) == 1:
                return equ_guards[0]
            else:
                return OrGuard(equ_guards)

    def z3_to_acc(self, z3acc):
        return str(z3acc) == "True"

    def z3_to_state(self, z3state):
        return str(z3state)

    def z3_to_label(self, z3label):
        return str(z3label)

    def z3_to_register(self, z3register):
        assert z3register is not self.ra.fresh
        if self.reg_context[z3register] is None:
            self.reg_context = Register(self.ra.registers.index(z3register))
        return self.reg_context[z3register]