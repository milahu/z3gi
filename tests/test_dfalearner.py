import unittest

from encode.fa import DFAEncoder
from tests.dfa_testscenario import *
from z3gi.learn.fa import FALearner
from z3gi.define.fa import DFA, MealyMachine
import model.fa
import z3

num_exp = 1


class DFALearnerTest(unittest.TestCase):
    def setUp(self):
        pass

    def test_sut1(self):
        self.check_scenario(sut_m1)

    def check_scenario(self, test_scenario):
        print("Scenario " + test_scenario.description)

        for i in range(0, num_exp):
            (succ, fa, model) = self.learn_model(test_scenario)

            self.assertTrue(succ, msg="Register Automaton could not be inferred")
            self.assertEqual(len(fa.states), test_scenario.nr_states,
                             "Wrong number of states.")
            self.assertEqual(len(fa.states), test_scenario.nr_states,
                             "Wrong number of registers.")
            exported = fa.export(model)
            print("Learned model:  \n", exported)
            self.assertEqual(len(exported.states()), test_scenario.nr_states,
                             "Wrong number of states in exported model. ")
            self.assertEqual(len(exported.registers()), test_scenario.nr_registers,
                             "Wrong number of registers in exported model. ")
            self.check_ra_against_obs(exported, test_scenario)

    def check_ra_against_obs(self, learned_fa, test_scenario):
        """Checks if the learned RA corresponds to the scenario observations"""
        for trace, acc in test_scenario.traces:
            self.assertEqual(learned_fa.accepts(trace), acc,
                             "Register automaton output doesn't correspond to observation {0}".format(str(trace)))

    def learn_model(self, test_scenario):
        labels = set()
        for label, _ in test_scenario.traces:
            labels.add(label)
        learner = FALearner(list(labels), encoder=DFAEncoder(),  verbose=True)
        for trace in test_scenario.traces:
            learner.add(trace)

        min_states = test_scenario.nr_states - 1
        max_states = test_scenario.nr_states + 1

        result = learner._learn_model(min_states, max_states)  #
        return result


        #
        # """
        # Visitor class for implementing procedures on inferred RAs.
        # """
        # class RaVisitor:
        #    def __init__(self):
        #       super().__init__()
        #    """
        #    Visits every location and transition in the register automaton.
        #    """
        #    def process(self, model, ra, labels, regs, states):
        #       to_visit = [ra.start]
        #       visited = []
        #       while (len(to_visit) > 0):
        #          loc = to_visit.pop(0)
        #          acc = model.eval(ra.output(loc))
        #          self._visit_location(loc, acc)
        #          visited.append(loc)
        #          next_trans  = []
        #          for l in labels:
        #             for r in regs:
        #                guard_enabled = model.eval(ra.guard(loc, l, r))
        #                if guard_enabled:
        #                   next_loc = model.eval(ra.transition(loc, l, r))
        #                   next_asg = model.eval(ra.update(loc, l))
        #                   next_trans.append((loc, l, r, next_asg, next_loc))
        #
        #          for (start_loc, label, guard, asg, end_loc) in next_trans:
        #             self._visit_transition(start_loc, label, guard, asg, end_loc)
        #             if end_loc not in visited and end_loc not in to_visit:
        #                to_visit.append(end_loc)
        #          # we sort according to the location strings so we get them in order
        #          to_visit.sort(key=lambda loc: str(loc))
        #    """
        #    Visits states in the RA in lexographical order starting from the initial location.
        #    """
        #    def _visit_location(self, loc, acc):
        #       raise NotImplementedError()
        #    """
        #    Visits transitions in the RA.
        #    """
        #    def _visit_transition(self, start_loc, label, guard, asg, end_loc):
        #       raise NotImplementedError()
        # class RaPrinter(RaVisitor):
        #    def __init__(self):
        #       super().__init__()
        #    """
        #    Prints location.
        #    """
        #    def _visit_location(self, loc, acc):
        #       print("{0}({1})".format(str(loc), "+" if acc == True else "-") )
        #    """
        #    Prints transition.
        #    """
        #    def _visit_transition(self, start_loc, label, guard, asg, end_loc):
        #       print("\t{0} -> {1}({2}) {3} {4}".format(str(start_loc), str(label), str(guard), str(asg), str(end_loc)))
        # # TODO it should probably store states/regs as strings
        # class SimpleRa():
        #    def __init__(self, states, loc_to_acc, loc_to_trans, registers):
        #       super().__init__()
        #       self.states = states
        #       self.loc_to_acc = loc_to_acc
        #       self.loc_to_trans = loc_to_trans
        #       self.register = registers
        #    def get_start_loc(self):
        #       return self.states[0]
        #    def get_states(self):
        #       return list(self.states)
        #    def get_transitions(self, loc, label=None):
        #       if label is None:
        #          return list(self.loc_to_trans[loc])
        #       else:
        #          return list([trans for trans in self.loc_to_trans[loc] if trans[1] == label])
        #    def get_registers(self):
        #       return list(self.registers)
        #    def get_acc(self, loc):
        #       return self.loc_to_acc[loc]
        # class NoTransitionTriggeredException(Exception):
        #    pass
        # class SimpleRaSimulator():
        #    def __init__(self, sra):
        #       super().__init__()
        #       self.ra = sra
        #    """
        #    Runs the given sequence of values on the RA.
        #    """
        #    def accepts(self, trace):
        #       init = -1
        #       reg_val =  dict()
        #       for reg in self.ra.get_registers():
        #          reg_val[reg] = init
        #       loc = self.ra.get_start_loc()
        #       for act in trace:
        #          next_transitions = self.ra.get_transitions(loc, act.label)
        #          # to define a fresh guard we need to know which register guards are present
        #          active_regs = [trans[2] for trans in next_transitions]
        #          n_loc = None
        #          for (_, _, guard, asg, next_loc) in next_transitions:
        #             if (self._is_satisfied(act, guard, active_regs, reg_val)):
        #                if not is_fresh(asg):
        #                   reg_val[asg] = act.value
        #                n_loc = next_loc
        #                break
        #          if n_loc is None:
        #             print("In location {0} with trans. {1}, \n reg vals {2} and crt val {3}".format(
        #                str(loc), str(next_transitions), str(reg_val), str(act.value)
        #             ))
        #             raise NoTransitionTriggeredException()
        #          else:
        #             loc = n_loc
        #       return self.ra.get_acc(loc)
        #    def _is_satisfied(self, act, guard, active_regs, reg_val):
        #       if is_fresh(guard):
        #          reg_vals = list([reg_val[reg] for reg in active_regs])
        #          return act.value not in reg_vals
        #       else:
        #          return act.value is reg_val[guard]
        # """
        # Builds a SRA from the inferred uninterpreted functions for the RA.
        # """
        # class SimpleRaBuilder(RaVisitor):
        #    def __init__(self):
        #       super().__init__()
        #       self.states = []
        #       self.loc_to_acc = dict()
        #       self.loc_to_trans = dict()
        #       self.registers = []
        #    def _visit_location(self, loc, acc):
        #       self.states.append(loc)
        #       self.loc_to_acc[loc] = acc
        #       if loc not in self.loc_to_trans:
        #          self.loc_to_trans[loc] = []
        #    def _visit_transition(self, start_loc, label, guard, asg, end_loc):
        #       self.loc_to_trans[start_loc].append((start_loc, label, guard, asg, end_loc))
        #       if not is_fresh(guard) and guard not in self.registers:
        #          self.registers.append(guard)
        #       if not is_fresh(asg) and asg not in self.registers:
        #          self.registers.append(asg)
        #    """
        #    Builds a SRA from the RA generated functions. It uses as states and registers the actual Z3 constants.
        #    """
        #    def build_ra(self):
        #       return SimpleRa(self.states, self.loc_to_acc, self.loc_to_trans, self.registers.sort(key=lambda reg: str(reg)))
        #
        #
        # def is_fresh(reg):
        #    return str(reg) == str("fresh")