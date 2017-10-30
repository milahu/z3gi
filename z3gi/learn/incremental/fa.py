from typing import Tuple

from z3 import z3

import define
from encode import IncrementalEncoder
from learn import Learner
from model import Automaton


class FAILearner(Learner):
    def __init__(self, encoder:IncrementalEncoder, solver=None, verbose=False, stop_unknown=False):
        super().__init__()
        if not solver:
            solver = z3.Solver()
        self.solver = solver
        self.encoder = encoder
        self.verbose = verbose
        self.stop_unknown = stop_unknown
        self.cst = []

    def add(self, trace):
        trace_const = self.encoder.trace(trace)
        #self.cst.append(trace_const)
        self.solver.add(trace_const)

    def model(self, min_states=1, max_states=20, old_definition:define.fa.FSM=None) -> Tuple[Automaton, define.fa.FSM]:
        if old_definition is not None:
            min_states = len(old_definition.states)
        (succ, fa, m) = self._learn_model(min_states=min_states,
                                        max_states=max_states)
        if succ:
            return fa.export(m), fa
        else:
            return  None

    def _learn_model(self, min_states=1, max_states=10):
        """generates the definition and model for an fa whose traces include the traces added so far
        In case of failure, the second argument of the tuple signals occurrence of a timeout"""
        for num_states in range(min_states, max_states + 1):
            #self.solver.reset()
            self.solver.add(z3.And(self.cst))
            self.solver.push()
            (states_const, aut_def) = self.encoder.automaton(num_states)
            if self.timeout is not None:
                self.solver.set("timeout", self.timeout)
            self.solver.add(states_const)
            result = self.solver.check()
            if self.verbose:
                print("Learning with {0} states. Result: {1}"
                  .format(num_states, result))
            if result == z3.sat:
                model = self.solver.model()
                self.solver.pop()
                return (True, aut_def, model)
            else:
                self.solver.pop()
                # timeout
                if result == z3.unknown and self.stop_unknown:
                    return (False, True, None)
                # TODO: process the unsat core?
                pass
        return (False, False, None)