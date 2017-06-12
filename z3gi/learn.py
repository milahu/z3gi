import collections

import z3

from z3gi import define, encode


class NonDeterminismError(Exception):
    pass


class LearnError(Exception):
    pass


class FSMLearner(object):
    def __init__(self, fsm, encoder=None, solver=None):
        if not encoder:
            encoder = encode.NestingEncoder
        self.encoder = encoder(fsm)
        if not solver:
            solver = z3.Solver()
        self.solver = solver
        self.cache = {}
        self.outputs = set()

    def add(self, inputs, outputs):
        if not isinstance(outputs, collections.Sequence) or len(outputs) == 1:
            self._add_single(inputs, outputs)
        else:
            expected_length = {
                (define.State,): lambda: len(inputs) + 1,
                (define.State, define.Input): lambda: len(inputs)
            }[define.domain(self.encoder.fsm.output)]()
            if not len(outputs) == expected_length or len(outputs) == 0:
                raise encode.EncodeError(inputs, outputs)
            self._add_iter(inputs, outputs)

    def _add_single(self, inputs, output):
        try:
            inputs = tuple(str(i) for i in inputs)
        except:
            raise encode.EncodeError(inputs)
        output = str(output)

        if inputs in self.cache and not self.cache[inputs] == output:
            raise NonDeterminismError(inputs, output)
        self.cache[inputs] = output
        self.outputs.add(output)

        domain = define.domain(self.encoder.fsm.output)
        if domain == (define.State, define.Input) and not inputs:
            raise encode.EncodeError('Can not encode empty string for output function over domain {0}'.format(domain))

        constraint = {
            (define.State,): lambda: self.encoder.output(self.encoder.state(inputs)) == define.output(output),
            (define.State, define.Input): lambda: self.encoder.output(self.encoder.state(inputs[:-1]),
                                                                      define.input(inputs[-1])) == define.output(output)
        }[domain]()
        self.solver.add(constraint)

    def _add_iter(self, inputs, outputs):
        for i in range(len(outputs)):
            if define.domain(self.encoder.fsm.output) == (define.State,):
                self._add_single(inputs[:i], outputs[i])
            elif define.domain(self.encoder.fsm.output) == (define.State, define.Input):
                self._add_single(inputs[:i + 1], outputs[i])

    def model(self, min_states=1, max_states=20):
        self.solver.add(self.encoder.outputs(self.outputs))
        for states in range(min_states, max_states + 1):
            self.solver.push()
            self.solver.add(self.encoder.states(["state{0}".format(i) for i in range(states)]))
            if self.solver.check() == z3.sat:
                return self.solver.model()
            else:
                self.solver.pop()
        raise LearnError("Not enough states: {0}".format(max_states))
