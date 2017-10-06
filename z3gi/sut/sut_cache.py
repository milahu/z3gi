from abc import abstractmethod, ABCMeta
from typing import List, Type
import itertools

from sut import SUT, TransducerObservation, Observation, MealyObservation
from utils import Tree



class Cache(metaclass=ABCMeta):

    @abstractmethod
    def from_cache(self, seq) -> Observation:
        pass

    @abstractmethod
    def update_cache(self, obs):
        pass

class IOCache(Cache):
    def __init__(self, obs_gen):
        self._tree = Tree(itertools.count(0))
        self._obs_gen = obs_gen

    def from_cache(self, seq):
        node = self._tree
        outs = []
        for inp in seq:
            if inp in node.children:
                out_node = node[[inp]]
                (out, node) = next(iter(out_node.children.items()))
                outs.append(out)
            else:
                return None
        trace = list(zip(seq, outs))
        return self._obs_gen(trace)

    def update_cache(self, obs: TransducerObservation):
        to_add = list(itertools.chain(*map(iter, obs.trace())))
        self._tree[to_add]

class CacheSUT(SUT):
    def __init__(self, sut:SUT, cache:Cache):
        self._sut = sut
        self._cache = cache

    def run(self, seq:List[object]):
        obs = self._cache.from_cache(seq)
        if obs is None:
            obs = self._sut.run(seq)
            self._cache.update_cache(obs)
            obs_t = self._cache.from_cache(seq)
            if obs_t is None or obs_t.trace() != obs.trace():
                print(obs.trace())
                print(self._cache._tree)
                print(obs_t.trace())
                exit(0)
        return obs

    def input_interface(self):
        return self._sut.input_interface()

#c = IOCache(MealyObservation)
#c.update_cache(MealyObservation([("a","oa"), ("a","ob")]))
#print(c._tree)
#c.update_cache(MealyObservation([("a","oa"), ("b","ob")]))
#print(c._tree)
#c.update_cache(MealyObservation([("b","ob"), ("b","ob")]))
#print(c._tree)
#
#print(c.from_cache(["b", "b"]))