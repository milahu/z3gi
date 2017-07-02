from abc import abstractmethod
from typing import List

from learn import Learner
from learn.ra import RALearner
from model import Automaton
from model.ra import IORegisterAutomaton, MutableIORegisterAutomaton, IORATransition, FreshGuard, NoAssignment, Fresh
from test import Tester

undefined = "undef"

class ActiveLearner():
    def __init__(self, model_learner:Learner, model_tester:Tester):
        self.learner = model_learner
        self.tester = model_tester

    def learn(self, inputs:List[str]):
        model = None
        while True:
            model = self._learn_new(self.learner, model)
            trace = self.tester.find_ce(model)
            if trace is not None:
                self.learner.add(trace)
            else:
                break

    @abstractmethod
    def _epsilon(self, inputs) -> Automaton:
        """Returns an epsilon initial model"""
        pass

    @abstractmethod
    def _learn_new(self, learner, old_model):
        """Learns a new model having recently invalidated an old model"""
        pass


class IORAActiveLearner(ActiveLearner):
    def __init__(self, model_learner:RALearner, model_tester:Tester):
        super().__init__(model_learner, model_tester)

    def _learn_new(self, learner: RALearner, old_model: IORegisterAutomaton):
        return learner.model(min_locations=len(old_model.states()), min_registers=len(old_model.registers()) )

    def _epsilon(self, inputs):
        mut_iora = MutableIORegisterAutomaton()
        init_loc = "q0"
        mut_iora.add_state(init_loc)
        for inp in inputs:
            mut_iora.add_transition(init_loc, IORATransition(
                init_loc, init_loc, FreshGuard(), NoAssignment(), undefined, Fresh(0), NoAssignment(), init_loc
            ))
        return mut_iora.to_immutable()




