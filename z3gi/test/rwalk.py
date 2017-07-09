from abc import ABCMeta, abstractmethod
from typing import List

import collections

import itertools

from model import Automaton, Transition
from model.ra import IORATransition, IORegisterAutomaton, EqualityGuard, OrGuard, Action, Register, FreshGuard, Fresh
from sut import SUT, ActionSignature, RASUT
from test import TestGenerator, Test, AcceptorTest, MealyTest, IORATest
import random
import pprint

rand = random.Random(0)

def rand_sel(l:List):
    return l[rand.randint(0, len(l)-1)]

class RWalkFromState(TestGenerator, metaclass=ABCMeta):
    def __init__(self, sut:SUT, test_gen, rand_length, prob_reset=0.2, rand_start_state=True):
        # the probability after each input added, that we stop adding further inputs to the random sequence
        # hence the rand_length is only the maximum length of the random sequence
        self.prob_reset = prob_reset
        self.rand_length = rand_length
        self.rand_start_state = rand_start_state
        self.sut = sut
        self.test_gen = test_gen

    def gen_test(self, model: Automaton) -> Test:
        """generates a test comprising an access sequence and a random sequence"""
        if model is None:
            # if the model is None, generate a test which includes all inputs (so at least we know the next generated
            # model will be input enabled)
            seq = self._generate_init()
        else:
            # select a random state
            if self.rand_start_state:
                crt_state = model.states()[rand.randint(0, len(model.states()) - 1)]
            else:
                crt_state = model.start_state()

            # get its access sequence (in the form of a sequence of transitions)
            trans_path = list(model.acc_trans_seq(crt_state))

            # from this state, do a random walk and generate a random sequence of transitions
            for _ in range(0, self.rand_length):
                transitions = model.transitions(crt_state)
                r_trans = transitions[rand.randint(0, len(transitions)-1)]
                crt_state = r_trans.end_state
                trans_path.append(r_trans)

            # instantiate the access and random sequences by extracting the sequence of inputs to be executed on the sut
            # for FSMs every sequence has a unique instantiation
            # for RAs, sequences may have different instantiations depending on the values chosen
            seq = self._generate_seq(model, trans_path)

        # run the sequence on inputs, which results on an observation and generate a corresponding test
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
    def __init__(self, sut: RASUT, rand_length, prob = ValueProb(0.4, 0.4, 0.2), rand_start_state=True):
        super().__init__(sut, IORATest, rand_length, rand_start_state)
        self.prob = prob

    def _generate_seq(self, model: IORegisterAutomaton, transitions:List[IORATransition]) -> List[Action]:
        """generates a sequence of inputs for the randomly chosen transition path"""
        act_arity = model.act_arity()
        seq = []
        values = list() # we use a list to preserve order/eliminate potential non-det
        reg_val = dict()
        for trans in transitions:
            if act_arity[trans.start_label] == 1:
                if isinstance(trans.guard, EqualityGuard) or isinstance(trans.guard, OrGuard):
                    inp_val = reg_val[trans.guard.registers()[0]]
                elif isinstance(trans.guard, FreshGuard):
                    # we have a fresh transition, which means we can either pick a fresh value or any past value
                    # as long as it is not stored in one of the guarded registers in this location
                    fresh_val = 0 if len(values) == 0 else max(values) + 1
                    active_regs =  list() if len(model.registers()) == 0 or len(trans.guard.registers()) == 0 else \
                        list(itertools.chain.from_iterable(
                            [tr.guard.registers() for tr in model.transitions(trans.start_state, trans.start_label)
                                              if tr is not trans]))
                    active_reg_vals = [reg_val[reg] for reg in active_regs]
                    selectable_reg_vals = [val for val in reg_val.values() if val not in active_reg_vals]
                    selectable_his_vals = [val for val in values if val not in active_reg_vals
                                           and val not in selectable_reg_vals]
                    inp_val = self.prob.select(selectable_reg_vals, selectable_his_vals, fresh_val)
                    if inp_val not in values:
                        values.append(inp_val)
                    inp = Action(trans.start_label, inp_val)
                    reg_val = trans.update(reg_val, inp)
                else:
                    raise Exception("Unkown guard")
            else:
                inp_val = None
            inp = Action(trans.start_label, inp_val)
            if act_arity[trans.output_label] == 1:
                # we are only interested in the case where the output value is fresh (hence the mapping is fresh).
                # In case of a "register" mapping, there can be no updates on registers (based on our encodings).
                if isinstance(trans.output_mapping, Fresh):
                    out_val = 0 if len(values) == 0 else max(values) + 1
                    if out_val not in values:
                        values.append(out_val)
                    out = Action(trans.output_label, out_val)
                    reg_val = trans.output_update(reg_val, out)

            seq.append(inp)
        return seq





