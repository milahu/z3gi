from abc import ABCMeta, abstractmethod

"""A basic abstract automaton model"""
class Automaton(metaclass=ABCMeta):
   def __init__(self, states, state_to_trans):
      super().__init__()
      self.states = states
      self.state_to_trans = state_to_trans

   def start_loc(self):
      return self.states[0]

   def states(self):
      return list(self.states)

   def transitions(self, state, label=None):
      if label is None:
         return list(self.state_to_trans[state])
      else:
         return list([trans for trans in self.state_to_trans[state] if trans.start_label == label])

   @abstractmethod
   def state(self, trace):
       pass

"""An automaton model that generates output"""
class Transducer(Automaton, metaclass=ABCMeta):
    def __init__(self, states, state_to_trans):
        Automaton.__init__(states, state_to_trans)

    @abstractmethod
    def outputs(self, trace):
        pass

"""An automaton model whose states are accepting/rejecting"""
class Acceptor(Automaton, metaclass=ABCMeta):
    def __init__(self, states, state_to_trans, state_to_acc):
        Automaton.__init__(states, state_to_trans)
        self.state_to_acc = state_to_acc

    def is_accepting(self, state):
        return self.state_to_acc[state]

    @abstractmethod
    def accepts(self, trace):
        pass


class Transition():
    def __init__(self, start_state, start_label, end_state):
        self.start_state = start_state
        self.start_label = start_label
        self.end_state = self.end_state