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

   def state(self, trace):
       """state function which also provides a basic implementation"""
       crt_state = self.start_state()
       tr_str = crt_state
       for symbol in trace:
           transitions = self.transitions(crt_state, symbol)
           fired_transitions = [trans for trans in transitions if trans.start_label == symbol]

           # the number of fired transitions can be more than one since we could have multiple equalities
           if len(fired_transitions) == 0:
               raise NoTransitionFired

           if len(fired_transitions) > 1:
               raise MultipleTransitionsFired

           fired_transition = fired_transitions[0]
           crt_state = fired_transition.end_state
           tr_str += " {0} {1}".format(symbol, crt_state)

       # print(tr_str)
       return crt_state

# Basic __str__ function which works for most FSMs.
   def __str__(self):
       str_rep = ""
       for state in self.states():
           str_rep += str(state) + "\n"
           for tran in self.transitions(state):
               str_rep += "\t"+tran.__str__(shortened=True) + "\n"

       return str_rep

class MutableAutomatonMixin(metaclass=ABCMeta):
    def add_state(self, state):
        if state not in self._states:
            self._states.append(state)

    def add_transition(self, state, transition):
        if state not in self._state_to_trans:
            self._state_to_trans[state] = []
        self._state_to_trans[state].append(transition)

    @abstractmethod
    def to_immutable(self) -> Automaton:
        pass

"""An automaton model that generates output"""
class Transducer(Automaton, metaclass=ABCMeta):
    def __init__(self, states, state_to_trans):
        super().__init__(states, state_to_trans)

    @abstractmethod
    def output(self, trace):
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

    def __str__(self):
        return str(self._state_to_acc) + "\n" + super().__str__()

class MutableAcceptorMixin(MutableAutomatonMixin, metaclass=ABCMeta):
    def add_state(self, state, accepts):
        super().add_state(state)
        self._state_to_acc[state] = accepts



"""The most basic transition class available"""
class Transition():
    def __init__(self, start_state, start_label, end_state):
        self.start_state = start_state
        self.start_label = start_label
        self.end_state = end_state

    def __str__(self, shortened=False):
        if not shortened:
            return "{0} {1} -> {2}".format(self.start_state, self.start_label, self.end_state)
        else:
            "{1} -> {2}".format(self.start_label, self.end_state)

"""Exception raised when no transition can be fired"""
class NoTransitionFired(Exception):
   pass

"""Exception raised when several transitions can be fired in a deterministic machine"""
class MultipleTransitionsFired(Exception):
    pass