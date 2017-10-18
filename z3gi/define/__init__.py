from abc import ABCMeta, abstractmethod

import z3

def dt_enum(name, elements):
    d = z3.Datatype(name)
    for element in elements:
        d.declare(element)
    d = d.create()
    return d, [d.__getattribute__(element) for element in elements]

def int_enum(name, elements):
    d = z3.IntSort()
    return d, [z3.IntVal(i) for i in range(1, len(elements) + 1)]

def declsort_enum(name, elements):
    d = z3.DeclareSort(name)
    return d, [z3.Const(element) for element in elements]

class Automaton(metaclass=ABCMeta):
    @abstractmethod
    def export(self, model):
        """Returns a z3gi.model for this automaton."""
        pass