import z3
from model.ra import *
from define import dt_enum, Automaton


class RegisterMachine(Automaton):
    def __init__(self, num_locations, num_registers, param_size):
        self.Location, self.locations = dt_enum('Location', ['location{0}'.format(i) for i in range(num_locations)])
        self.Register, self.registers = dt_enum('Register',
                                             ['register{0}'.format(i) for i in range(num_registers)] + ['fresh'])
        self.param_size = param_size

class RegisterAutomaton(RegisterMachine):

    def __init__(self, labels, param_size, num_locations, num_registers):
        super().__init__(num_locations, num_registers, param_size)
        self.Label, elements = dt_enum('Label', labels)
        self.labels = {labels[i]: elements[i] for i in range(len(labels))}
        self.start = self.locations[0]
        self.fresh = self.registers[-1]
        self.transition = z3.Function('transition', self.Location, self.Label, self.Register, self.Location)
        self.output = z3.Function('output', self.Location, z3.BoolSort())
        self.used = z3.Function('used', self.Location, self.Register, z3.BoolSort())
        self.update = z3.Function('update', self.Location, self.Label, self.Register)

    def export(self, model : z3.ModelRef) -> RegisterAutomaton:
        builder = RegisterAutomatonBuilder(self)
        ra = builder.build_ra(model)
        return ra


class IORegisterAutomaton(RegisterMachine):
    def __init__(self, input_labels, output_labels, param_size, num_locations, num_registers):
        super().__init__(num_locations, num_registers, param_size)
        labels = input_labels + output_labels
        self.Label, elements = dt_enum('Label', input_labels + output_labels)
        self.labels = {labels[i]: elements[i] for i in range(len(labels))}
        self._input_labels =  [self.labels[lbl] for lbl in input_labels]
        self.sink = self.locations[-1]
        self.start = self.locations[0]
        self.fresh = self.registers[-1]
        self.transition = z3.Function('transition', self.Location, self.Label, self.Register, self.Location)
        self.output = z3.Function('output', self.Location, z3.BoolSort())
        self.used = z3.Function('used', self.Location, self.Register, z3.BoolSort())
        self.update = z3.Function('update', self.Location, self.Label, self.Register)
        self.loctype = z3.Function('loctype', self.Location, z3.BoolSort())


    def export(self, model : z3.ModelRef) -> IORegisterAutomaton:
        builder = IORegisterAutomatonBuilder(self)
        ra = builder.build_ra(model)
        return ra


class IORegisterAutomaton2(Automaton):

    def __init__(self, inputs, outputs, num_locations, num_registers):
        self.Input, self.inputs = dt_enum('Input', inputs)
        self.Output, self.outputs = dt_enum('Output', outputs)
        self.Location, self.locations = dt_enum('Location', ['location{0}'.format(i) for i in range(num_locations)])
        self.Register, self.registers = dt_enum('Register', ['register{0}'.format(i) for i in range(num_registers)] + ['fresh'])
        self.start = self.locations[0]
        self.fresh = self.registers[-1]
        self.transition = z3.Function('transition', self.Location, self.Input, self.Register, self.Location)
        self.output = z3.Function('output', self.Location, self.Input, self.Register, self.Output)
        self.register = z3.Function('register', self.Location, self.Input, self.Register, self.Register)
        self.used = z3.Function('used', self.Location, self.Register, z3.BoolSort())
        self.update = z3.Function('update', self.Location, self.Input, self.Register)

class Mapper(object):
    def __init__(self, ra):
        self.Value = z3.DeclareSort('Value')
        self.Element = z3.DeclareSort('Element')
        self.start = self.element(0)
        self.init = self.value("_")
        self.map = z3.Function('map', self.Element, ra.Location)
        self.valuation = z3.Function('valuation', self.Element, ra.Register, self.Value)

    def value(self, name):
        return z3.Const("v"+str(name), self.Value)

    def element(self, name):
        return z3.Const("n"+str(name), self.Element)

class RegisterAutomatonBuilder(object):
    """
    Builder class that construct a register automaton out of a model definition.
    """
    def __init__(self, ra : RegisterAutomaton):
        super().__init__()
        self.ra = ra

    def build_ra(self, model):
        mut_ra = MutableRegisterAutomaton()
        translator = RATranslator(self.ra)
        for z3state in self.ra.locations:
            self._add_state(model, translator, mut_ra, z3state)
            for z3label in self.ra.labels.values():
                self._add_transitions(model, translator, mut_ra, z3state, z3label)
        mut_ra.generate_acc_seq()
        mut_ra.set_act_arities(self.ra.param_size)
        return mut_ra.to_immutable()

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


class IORegisterAutomatonBuilder(object):
    """
    Builder class that construct a register automaton out of a model definition.
    """
    def __init__(self, ra : IORegisterAutomaton):
        super().__init__()
        self.ra = ra


    def build_ra(self, model):
        mut_ra = MutableIORegisterAutomaton()
        translator = RATranslator(self.ra)

        z3input_states = [z3state for z3state in self.ra.locations if
            translator.z3_to_bool(model.eval(
                z3.And(self.ra.loctype(z3state), z3state != self.ra.sink)))]

        # we cannot use 'is not', since 'is not' compares references, not values and model.eval produces a
        # different reference
        z3input_labels = [z3label for z3label in self.ra.labels.values() if
                          translator.z3_to_bool(model.eval(
                              self.ra.transition(self.ra.start, z3label, self.ra.fresh) != self.ra.sink))
                          ]
        z3output_labels = [z3label for z3label in self.ra.labels.values() if z3label not in z3input_labels]
        print("Input labels ", z3input_labels, "; Output labels", z3output_labels,
              "Input states ", z3input_states, "; Output and sink states",
              [z3state for z3state in self.ra.locations if z3state not in z3input_states])

        for z3state in z3input_states:
            self._add_state(translator, mut_ra, z3state)
            for z3label in z3input_labels:
                self._add_transitions(model, translator, mut_ra, z3state, z3label, z3output_labels)
        mut_ra.generate_acc_seq()
        mut_ra.set_act_arities(self.ra.param_size)
        return mut_ra.to_immutable()

    def _add_state(self, translator, mut_ra, z3state):
        mut_ra.add_state(translator.z3_to_state(z3state))

    def _add_transitions(self, model, translator, mut_ra, z3state, z3label, z3output_labels):
        z3end_state_to_guards = dict()
        enabled_z3guards = [guard for guard in self.ra.registers if
                            translator.z3_to_bool(model.eval(self.ra.used(z3state, guard))) or
                            guard is self.ra.fresh]

        for z3guard in enabled_z3guards:
            z3out_state = model.eval(self.ra.transition(z3state, z3label, z3guard))

            if z3out_state not in z3end_state_to_guards:
                z3end_state_to_guards[z3out_state] = []
            z3end_state_to_guards[z3out_state].append(z3guard)
        update = model.eval(self.ra.update(z3state, z3label))
        used_z3regs = [reg for reg in enabled_z3guards if reg is not self.ra.fresh]

        #print("For {0} we have the transitions \n {1}".format(z3state, z3end_state_to_guards))
        for (z3out_state, z3guards) in z3end_state_to_guards.items():
            # a transition which makes an assignment is never merged
            if self.ra.fresh in z3guards and not translator.z3_to_bool(model.eval(update == self.ra.fresh)):
                self._add_transition(model, translator, mut_ra, z3state, z3label,
                                     [self.ra.fresh], update, z3out_state,
                                     z3output_labels, used_z3regs)
                z3guards.remove(self.ra.fresh)
            if len(z3guards) > 0:
                self._add_transition(model, translator, mut_ra, z3state, z3label,
                                     z3guards, None, z3out_state,
                                     z3output_labels, used_z3regs)

    def _add_transition(self, model, translator, mut_ra, z3start_state, z3label,
                        z3disjguards, z3input_update, z3out_state, output_labels, used_z3regs):

        enabled_z3guards = [guard for guard in self.ra.registers if
                            translator.z3_to_bool(model.eval(self.ra.used(z3out_state, guard))) or
                            guard is self.ra.fresh]

        active_z3action = [(output_label, guard) for output_label in output_labels for guard in enabled_z3guards
                         if translator.z3_to_bool(model.eval(self.ra.transition(z3out_state, output_label, guard)
                                                             != self.ra.sink))]
        if len(active_z3action) != 1:
            raise Exception("Exactly one transition should not lead to sink state. "
                            "From location {0} there are {1} transitions which don't lead to sink {2}. \n"
                            "Namely: {3}"
                            "\n\n Model: {4}"
                            .format(z3out_state, len(active_z3action), self.ra.sink, enabled_z3guards, model))

        (z3output_label, z3output_guard) = active_z3action[0]
        z3end_state = model.eval(self.ra.transition(z3out_state, z3output_label, z3output_guard))
        z3output_update = model.eval(self.ra.update(z3out_state, z3output_label))
        output_mapping = None if self.ra.param_size[translator.z3_to_label(z3output_label)] == 0 \
                              else  translator.z3_to_mapping(z3output_guard)

        transition = IORATransition(translator.z3_to_state(z3start_state),
                                    translator.z3_to_label(z3label),
                                    translator.z3_to_guard(z3disjguards, used_z3regs),
                                    translator.z3_to_assignment(z3input_update),
                                    translator.z3_to_label(z3output_label),
                                    output_mapping,
                                    translator.z3_to_assignment(z3output_update),
                                    translator.z3_to_state(z3end_state),
                                    )
        mut_ra.add_transition(translator.z3_to_state(z3start_state), transition)

class RATranslator(object):
    """Provides translation from z3 constants to RA elements. """
    def __init__(self, ra):
        self.reg_context = dict()
        self.ra = ra

    def z3_to_assignment(self, z3asg):
        if (z3asg is None) or (z3asg == self.ra.fresh):
            asg = NoAssignment()
        else:
            asg = RegisterAssignment(self.z3_to_register(z3asg))
        return asg

    def z3_to_guard(self, z3guards, enabled_z3regs):
        z3guard_regs = [z3reg for z3reg in z3guards if z3reg is not self.ra.fresh]
        if self.ra.fresh in z3guards:
            diff_from = [self.z3_to_register(z3reg) for z3reg in enabled_z3regs
                         if z3reg not in z3guard_regs and z3reg is not self.ra.fresh]
            return FreshGuard(diff_from)
        else:
            equ_guards = [EqualityGuard(self.z3_to_register(guard_reg)) for guard_reg in z3guard_regs]
            if len(equ_guards) == 1:
                return equ_guards[0]
            else:
                return OrGuard(equ_guards)

    def z3_to_mapping(self, z3guard):
        if z3guard is self.ra.fresh:
            return Fresh(0)
        else:
            return self.z3_to_register(z3guard)

    def z3_to_bool(self, z3bool):
        return str(z3bool) == "True"

    def z3_to_state(self, z3state):
        return "l"+str(self.ra.locations.index(z3state))

    def z3_to_label(self, z3label):
        return str(z3label)

    def z3_to_register(self, z3register):
        if str(z3register) == "fresh":
            raise Exception
        assert z3register is not self.ra.fresh
        if str(z3register) not in self.reg_context:
            self.reg_context[str(z3register)] = Register(self.ra.registers.index(z3register))
        return self.reg_context[str(z3register)]
