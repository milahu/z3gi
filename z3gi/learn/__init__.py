from abc import ABCMeta, abstractmethod

class Learner(metaclass=ABCMeta):
    @abstractmethod
    def add(self, trace):
        pass

    @abstractmethod
    def model(self):
        pass