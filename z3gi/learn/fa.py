from typing import Tuple

import z3
from learn import Learner
from model import Automaton, InvalidAutomaton
import define.fa

class FALearner(Learner):
    def __init__(self, encoder, solver=None, verbose=False):
        super().__init__()
        if not solver:
            solver = z3.Solver()
        self.solver = solver
        self.encoder = encoder
        self.verbose = verbose

    def add(self, trace):
        self.encoder.add(trace)

    def model(self, min_states=1, max_states=25, old_definition:define.fa.FSM=None, ensure_min=False) -> Tuple[Automaton, define.fa.FSM]:
        if old_definition is not None:
            min_states = len(old_definition.states)
        (succ, fa, m) = self._learn_model(min_states=min_states,
                                        max_states=max_states, ensure_min=ensure_min)
        self.solver.reset()
        if succ:
            try:
                return fa.export(m), fa
            except InvalidAutomaton:
                print("Constructed automaton is invalid ", m)
                return None
        else:
            return  None

    def _learn_model(self, min_states, max_states, ensure_min=True):
        """generates the definition and model for an fa whose traces include the traces added so far
        In case of failure, the second argument of the tuple signals occurrence of a timeout"""
        for num_states in range(min_states, max_states + 1):
            fa, constraints = self.encoder.build(num_states)
            self.solver.reset()
            self.solver.set(":random-seed", 0)
            self.solver.add(constraints)
            if self.timeout is not None:
                self.solver.set("timeout", self.timeout)
            result = self.solver.check()
            if self.verbose:
                print("Learning with {0} states. Result: {1}"
                  .format(num_states, result))
            if result == z3.sat:
                model = self.solver.model()
                return (True, fa, model)
            else:
                # timeout, if minimality guarantee is required, we have to stop here
                if result == z3.unknown and ensure_min:
                    return (False, True, None)
                # TODO: process the unsat core?
                pass
        return (False, False, None)