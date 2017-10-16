from abc import abstractmethod, ABCMeta
from typing import List, Type
import itertools

from sut import SUT, TransducerObservation, Observation, MealyObservation, AcceptorObservation
from utils import Tree



class Cache(metaclass=ABCMeta):

    @abstractmethod
    def from_cache(self, seq) -> Observation:
        pass

    @abstractmethod
    def update_cache(self, obs):
        pass

    @abstractmethod
    def obs_iterator(self):
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

    def obs_iterator(self):
        next_seqs = [[]]
        while len(next_seqs) > 0:
            seq = next_seqs.pop()
            obs = self.from_cache(seq)
            if obs is None:
                print(self._tree)
                print(seq)
                exit(0)
            seq_node = self._tree[ list(itertools.chain(*map(iter, obs.trace())))]
            if len(seq_node.children) > 0:
                for inp in seq_node.children.keys():
                    next_seqs.append(seq + [inp])
            else:
                yield obs




class AcceptorCache(Cache):
    def __init__(self, obs_gen):
        self._tree = Tree(itertools.count(0))
        self._obs_gen = obs_gen
        self._acc = {}

    def from_cache(self, seq) -> Observation:
        node = self._tree[seq]
        if node in self._acc:
            return self._obs_gen(seq, self._acc[node])
        else:
            return None

    def update_cache(self, obs: AcceptorObservation):
        node = self._tree[obs.inputs()]
        self._acc[node] = obs.acc


    def obs_iterator(self):
        next_seqs = [[]]
        while len(next_seqs) > 0:
            seq = next_seqs.pop()
            seq_node = self._tree[seq]
            if len(seq_node.children) > 0:
                for inp in seq_node.children.keys():
                    next_seqs.append(seq + [inp])
            else:
                obs = self.from_cache(seq)
                #if obs is None:
                #    print(seq)
                #    print(self._tree)
                #    exit(0)
                yield obs

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