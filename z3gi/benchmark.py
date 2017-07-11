from abc import ABCMeta
from typing import Tuple, List, Dict

import collections

from learn import Learner
from sut import SUTType, ScalableSUTClass
from test import TestGenerator
from learn.algorithm import learn_mbt, Statistics

SutDesc = collections.namedtuple("SutDesc", 'class type size')

class Benchmark:
    def __init__(self):
        self.suts:List[Tuple[ScalableSUTClass, SUTType]] = []
        self.learn_setup: Dict[SUTType, Tuple[Learner, type]] = {}

    def add_sut(self, sut_class:ScalableSUTClass, sut_type=None):
        if sut_type is None:
            for st in list(SUTType):
                if sut_class.new_sut(st, 1) is not None:
                    self.suts.append((sut_class, st))
        else:
            if sut_class.new_sut(sut_type, 1) is None:
                raise Exception(" Added type not implemented by the sut class")
            self.suts.append((sut_class, sut_type))
        return self

    def add_setup(self, sut_type, sut_learner, sut_tester):
        self.learn_setup[sut_type] = (sut_learner, sut_tester)
        return self

    def _run_benchmark(self, sut_class:ScalableSUTClass, sut_type:SUTType, learner:Learner,
                       test_gen:type, max_texts:int, timeout:int) -> List[Tuple[SutDesc, Statistics]]:
        results = []
        learner.set_timeout(timeout)
        size = 1
        while True:
            sut = sut_class.new_sut(sut_type, size)
            tester = test_gen(sut)
            (model, statistics) = learn_mbt(learner, tester, max_texts)
            if model is None:
                break
            else:
                results.append(SutDesc(sut_class, sut_type, size), statistics)
        return  results

    def run_benchmarks(self, max_texts:int, timeout:int) -> List[Tuple[SutDesc, Statistics]]:
        results = []
        for sut_class, sut_type in self.suts:
            (learner, tester) = self.learn_setup[sut_type]
            res = self._run_benchmark(sut_class, sut_type, learner, tester, max_texts, timeout)
            results.extend(res)
        return results


