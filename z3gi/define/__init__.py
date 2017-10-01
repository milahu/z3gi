from abc import ABCMeta, abstractmethod

import z3


def enum(name, elements):
    d = z3.Datatype(name)
    for element in elements:
        d.declare(element)
    d = d.create()
    return d, [d.__getattribute__(element) for element in elements]

class Automaton(metaclass=ABCMeta):
    @abstractmethod
    def export(self, model):
        """Returns a z3gi.model for this automaton."""
        pass