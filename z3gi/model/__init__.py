from abc import ABCMeta, abstractmethod

"""A basic abstract automaton model"""
class Automaton(metaclass=ABCMeta):
   def __init__(self, states, state_to_trans):
      super().__init__()
      self._states = states
      self._state_to_trans = state_to_trans

   def start_state(self):
      return self._states[0]

   def states(self):
      return list(self._states)

   def transitions(self, state, label=None):
      if label is None:
         return list(self._state_to_trans[state])
      else:
         return list([trans for trans in self._state_to_trans[state] if trans.start_label == label])

   @abstractmethod
   def state(self, trace):
       pass

"""An automaton model that generates output"""
class Transducer(Automaton, metaclass=ABCMeta):
    def __init__(self, states, state_to_trans):
        super().__init__(states, state_to_trans)

    @abstractmethod
    def outputs(self, trace):
        pass

"""An automaton model whose states are accepting/rejecting"""
class Acceptor(Automaton, metaclass=ABCMeta):
    def __init__(self, states, state_to_trans, state_to_acc):
        super().__init__(states, state_to_trans)
        self._state_to_acc = state_to_acc

    def is_accepting(self, state):
        return self._state_to_acc[state]

    def accepts(self, trace):
        state = self.state(trace)
        is_acc = self.is_accepting(state)
        return is_acc

"""The most basic transition class available"""
class Transition():
    def __init__(self, start_state, start_label, end_state):
        self.start_state = start_state
        self.start_label = start_label
        self.end_state = end_state


"""Exception raised when no transition can be fired"""
class NoTransitionFired(Exception):
   pass

"""Exception raised when several transitions can be fired in a deterministic machine"""
class MultipleTransitionsFired(Exception):
    pass

