import unittest

from tests.ra_testscenario import *
from z3gi.learn.ra import RALearner
from z3gi.define.ra import RegisterAutomaton
import model.ra
import z3

num_exp = 1

class RaLearnerTest(unittest.TestCase):

    def setUp(self):
        pass


    def test_sut1(self):
        self.check_scenario(sut_m1)

    def test_sut2(self):
        self.check_scenario(sut_m2)

    def test_sut3(self):
        self.check_scenario(sut_m3)

    def test_sut4(self):
        self.check_scenario(sut_m4)

    def test_sut5(self):
        self.check_scenario(sut_m5)

    def check_scenario(self, test_scenario : RaTestScenario):
        print("Scenario " + test_scenario.description)

        for i in range(0,num_exp):
            (succ, ra, model) = self.learn_model(test_scenario)

            self.assertTrue(succ, msg="Register Automaton could not be inferred")
            self.assertEqual(len(ra.locations), test_scenario.nr_locations,
                             "Wrong number of locations." )
            self.assertEqual(len(ra.locations), test_scenario.nr_locations,
                             "Wrong number of registers.")
            exported = ra.export(model)
            print("Learned model:  \n",exported)
            self.assertEqual(len(exported.states()), test_scenario.nr_locations,
                              "Wrong number of locations in exported model. ")
            self.assertEqual(len(exported.registers()), test_scenario.nr_registers,
                              "Wrong number of registers in exported model. ")
            self.check_ra_against_obs(exported, test_scenario)


    def check_ra_against_obs(self, learned_ra: model.ra.RegisterAutomaton, test_scenario : RaTestScenario):
        """Checks if the learned RA corresponds to the scenario observations"""
        for trace, acc in test_scenario.traces:
            self.assertEqual(learned_ra.accepts(trace), acc,
                             "Register automaton output doesn't correspond to observation {0}".format(str(trace)))
    
    def learn_model(self, test_scenario : RaTestScenario) -> \
            (bool, RegisterAutomaton, z3.ModelRef):
        ralearner = RALearner(labels, verbose=True)
        for trace in test_scenario.traces:
            ralearner.add(trace)

        min_locations = test_scenario.nr_locations - 1
        max_locations = test_scenario.nr_locations + 1

        result = ralearner._learn_model(min_locations, max_locations, test_scenario.nr_registers + 1)  #
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
#    def process(self, model, ra, labels, regs, locations):
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
#    Visits locations in the RA in lexographical order starting from the initial location.
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
# # TODO it should probably store locations/regs as strings
# class SimpleRa():
#    def __init__(self, locations, loc_to_acc, loc_to_trans, registers):
#       super().__init__()
#       self.locations = locations
#       self.loc_to_acc = loc_to_acc
#       self.loc_to_trans = loc_to_trans
#       self.register = registers
#    def get_start_loc(self):
#       return self.locations[0]
#    def get_locations(self):
#       return list(self.locations)
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
#       self.locations = []
#       self.loc_to_acc = dict()
#       self.loc_to_trans = dict()
#       self.registers = []
#    def _visit_location(self, loc, acc):
#       self.locations.append(loc)
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
#    Builds a SRA from the RA generated functions. It uses as locations and registers the actual Z3 constants.
#    """
#    def build_ra(self):
#       return SimpleRa(self.locations, self.loc_to_acc, self.loc_to_trans, self.registers.sort(key=lambda reg: str(reg)))
#
#
# def is_fresh(reg):
#    return str(reg) == str("fresh")