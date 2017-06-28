from abc import ABCMeta, abstractmethod

class Encoder(metaclass=ABCMeta):
    @abstractmethod
    def add(self, trace):
        pass

    @abstractmethod
    def build(self, *args):
        pass