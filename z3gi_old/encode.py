import itertools
import collections
import abc
import z3

from z3gi_old import define


class EncodeError(Exception):
    pass


class FSMEncoder(metaclass=abc.ABCMeta):
    def __init__(self, fsm):
        if not isinstance(fsm, define.Automaton):
            raise EncodeError(fsm)
        self.fsm = fsm
        self._init()

    @abc.abstractmethod
    def _init(self):
        pass

    def state(self, access):
        if not isinstance(access, collections.Iterable):
            raise EncodeError(access)
        return self._state(access)

    @abc.abstractmethod
    def _state(self, access):
        pass

    def transition(self, state, input):
        if not (isinstance(state, z3.ExprRef) and state.sort() == define.State):
            raise EncodeError(state)
        if not (isinstance(input, z3.ExprRef) and input.sort() == define.Input):
            raise EncodeError(input)

        return self.fsm.transition(state, input)

    def output(self, state, input=None):
        if not (isinstance(state, z3.ExprRef) and state.sort() == define.State):
            raise EncodeError(state)
        domain = define.domain(self.fsm.output)
        if not ({(define.State,): lambda: input is None,
                 (define.State, define.Input): lambda: (isinstance(input, z3.ExprRef) and input.sort() == define.Input)
                 }[domain]()):
            raise EncodeError(input)

        return {
            (define.State,): lambda: self.fsm.output(state),
            (define.State, define.Input): lambda: self.fsm.output(state, input)
        }[domain]()

    def states(self, names):
        if not isinstance(names, collections.Iterable) or len(names) < 1:
            raise EncodeError(names)

        states = [define.state(name) for name in names]

        # free variables in z3's ForAll need to be declared
        state = define.state()
        input = define.input()

        return z3.And([z3.Int('n') == len(states),
                       self.fsm.start == states[0],
                       z3.Distinct([define.state(s) for s in states]),
                       z3.ForAll([state, input],
                                 z3.Or([self.fsm.transition(state, input) == s for s in states]),
                                 patterns=[self.fsm.transition(state, input)]),
                       self._states(states)])

    @abc.abstractmethod
    def _states(self, states):
        pass

    @classmethod
    def outputs(cls, names):
        if not isinstance(names, collections.Iterable) or not names:
            raise EncodeError
        outputs = [define.output(name) for name in names]
        return z3.Distinct(outputs)


class NestingFSMEncoder(FSMEncoder):
    def _init(self):
        pass

    def _state(self, access):
        if not access:
            return self.fsm.start
        return self.fsm.transition(self._state(access[:-1]), define.input(access[-1]))

    def _states(self, states):
        return True


class MappingFSMEncoder(FSMEncoder):
    def _init(self):
        self._trie = MappingFSMEncoder.Node(itertools.count(0))
        self._statemap = define.StateMapper()

    def _state(self, access):
        node = self._trie[tuple(access)]
        return self._statemap(define.element(node.id))

    def _states(self, states):
        # free variables used in z3's ForAll need to be declared
        element = define.element()
        return z3.And([z3.ForAll(element,
                                 z3.Or([self._statemap(element) == s for s in states]),
                                 patterns=[self._statemap(element)])] +
                      [self.transition(self._statemap(define.element(n.id)), define.input(i)) == self._statemap(
                          define.element(c.id))
                       for n, i, c in self._trie.transitions()])

    class Node(object):
        def __init__(self, counter):
            self.id = next(counter)
            self.counter = counter
            self.children = {}

        def __getitem__(self, access):
            node = self
            for input in access:
                input = str(input)
                if input not in node.children:
                    node.children[input] = MappingFSMEncoder.Node(self.counter)
                node = node.children[input]
            return node

        def __iter__(self):
            yield self
            for child in itertools.chain(*map(iter, self.children.values())):
                yield child

        def transitions(self):
            for node in self:
                for input in node.children:
                    yield node, input, node.children[input]
