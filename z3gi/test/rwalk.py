from abc import ABCMeta, abstractmethod
from typing import List

import collections

import itertools

from model import Automaton, Transition
from model.ra import IORATransition, IORegisterAutomaton, EqualityGuard, OrGuard, Action, Register
from sut import SUT, ActionSignature
from test import TestGenerator, Test, AcceptorTest, MealyTest, IORATest
import random

rand = random.Random(0)

def rand_sel(l:List):
    return l[rand.randint(0, len(l)-1)]

class RWalkFromState(TestGenerator, metaclass=ABCMeta):
    def __init__(self, sut:SUT, test_gen, rand_length, rand_start_state=True):
        self.rand_length = rand_length
        self.rand_start_state = rand_start_state
        self.sut = sut
        self.test_gen = test_gen

    def gen_test(self, model: Automaton) -> Test:
        """generates a test comprising an access sequence and a random sequence"""
        if model is None:
            seq = self._generate_init()
        else:
            if self.rand_start_state:
                crt_state = model.states()[rand.randint(0, len(model.states()) - 1)]
            else:
                crt_state = model.start_state()

            trans_path = list(model.acc_trans_seq(crt_state))
            for _ in range(0, self.rand_length):
                transitions = model.transitions(crt_state)
                r_trans = transitions[rand.randint(0, len(transitions)-1)]
                crt_state = r_trans.end_state
                trans_path.append(r_trans)
            seq = self._generate_seq(model, trans_path)
        obs = self.sut.run(seq)
        test = self.test_gen(obs.trace())
        return test

    def _generate_init(self):
        """generates a sequence covering all input elements in the sut interface"""
        seq = []
        for abs_inp in self.sut.input_interface():
            cnt = 0
            # if it's RA stuff
            if isinstance(abs_inp, ActionSignature):
                if abs_inp.num_params == 0:
                    val = None
                else:
                    val = cnt
                    cnt += 1
                seq.append(Action(abs_inp.label, val))
            elif isinstance(abs_inp, str):
                seq.append(abs_inp)
            else:
                raise Exception("Unrecognized type")
        return seq

    @abstractmethod
    def _generate_seq(self, model: Automaton, trans_path:List[Transition]):
        """generates a sequence of inputs for the randomly chosen transition path"""
        pass

# FSM versions of the algorithm
class FSMRWalkFromState(RWalkFromState, metaclass=ABCMeta):
    def __init__(self, sut: SUT, test_gen, rand_length, rand_start_state=True):
        super().__init__(sut, test_gen, rand_length, rand_start_state)

    def _generate_seq(self, model: Automaton, trans_path:List[Transition]):
        return [trans.start_label for trans in trans_path]


class DFARWalkFromState(RWalkFromState):
    def __init__(self, sut:SUT, rand_length, rand_start_state=True):
        super().__init__(self, sut, AcceptorTest, rand_length, rand_start_state)

class MealyRWalkFromState(RWalkFromState):
    def __init__(self, sut:SUT, rand_length, rand_start_state=True):
        super().__init__(self, sut, MealyTest, rand_length, rand_start_state)

class ValueProb(collections.namedtuple("ValueProb", ("history", "register", "fresh"))):
    def select(self, reg_vals:List[int], his_vals:List[int], fresh_value):
        pick = rand.random()
        if pick < self.register and len(reg_vals) > 0:
            return reg_vals[rand.randint(0, len(reg_vals)-1)]
        elif pick >= self.register and pick < self.register + self.history and len(his_vals) > 0:
            return his_vals[rand.randint(0, len(his_vals) - 1)]
        else:
            return fresh_value


class IORARWalkFromState(RWalkFromState):
    def __init__(self, sut: SUT, rand_length, prob = ValueProb(0.4, 0.4, 0.2), rand_start_state=True):
        super().__init__(sut, IORATest, rand_length, rand_start_state)
        self.prob = prob

    def _generate_seq(self, model: IORegisterAutomaton, transitions:List[IORATransition]):
        """generates a sequence of inputs for the randomly chosen transition path"""
        seq = []
        values = set() # we may consider using lists to preserve order (sets cause randomness)
        reg_val = dict()
        for trans in transitions:
            if isinstance(trans.guard, EqualityGuard) or isinstance(trans.guard, OrGuard):
                inp_val = reg_val[trans.guard.registers()[0]]
            else:
                # we have a fresh transition, which means we can either pick a fresh value or any past value
                # as long as it is not stored in one of the guarded registers in this location
                fresh_val = 0 if len(values) == 0 else max(values) + 1
                r_list = list(itertools.chain((tr.guard.registers() for tr in
                                            model.transitions(trans.start_state))))
                print(r_list)

                active_regs =  set() if len(model.registers()) == 0 else \
                    set(itertools.chain([tr.guard.registers() for tr in model.transitions(trans.start_state)]))
                active_reg_vals = [reg_val[reg] for reg in active_regs]
                selectable_reg_vals = [val for val in reg_val.values() if val not in active_reg_vals]
                selectable_his_vals = [val for val in values if val not in active_reg_vals
                                       and val not in selectable_reg_vals]
                inp_val = self.prob.select(selectable_reg_vals, selectable_his_vals, fresh_val)
                values.add(inp_val)
            inp = Action(trans.start_label, inp_val)
            reg_val = trans.update(reg_val, inp)
            if isinstance(trans.output_mapping, Register):
                out_val = reg_val[trans.output_mapping]
            else:
                out_val = 0 if len(values) == 0 else max(values) + 1
                values.add(out_val)
            out = Action(trans.output_label, out_val)
            reg_val = trans.output_update(reg_val, out)
            seq.append(inp)
        return seq








