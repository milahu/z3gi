from unittest import TestCase

from z3gi_old import define, encode


class TestMappingEncoder(TestCase):
    def test_state(self):
        for fsm in [define.MooreMachine(), define.MealyMachine()]:
            encoder = encode.MappingFSMEncoder(fsm)
            tests = {'': encoder._statemap(define.element(0)),
                     'ab': encoder._statemap(define.element(2)),
                     (1, 2): encoder._statemap(define.element(4)),
                     'a': encoder._statemap(define.element(1)),
                     '1': encoder._statemap(define.element(3))}
            for key in ['', 'ab', (1, 2), 'a', '1']:
                state = encoder.state(key)
                self.assertTrue(state.sort().eq(define.State))
                self.assertEqual(state, tests[key])

    def test_transition(self):
        for fsm in [define.MooreMachine(), define.MealyMachine()]:
            encoder = encode.MappingFSMEncoder(fsm)
            tests = {'ab': fsm.transition(encoder.state('a'), define.input('b')),
                     (1, 2): fsm.transition(encoder.state((1,)), define.input(2))}
            encoder = encode.MappingFSMEncoder(fsm)
            for key, value in tests.items():
                self.assertTrue(encoder.transition(encoder.state(key[:-1]), define.input(key[-1])).eq(tests[key]))

    def test_output(self):
        fsm = define.MooreMachine()
        encoder = encode.MappingFSMEncoder(fsm)
        tests = {'': fsm.output(encoder.state('')),
                 'ab': fsm.output(encoder.state('ab')),
                 (1, 2): fsm.output(encoder.state((1, 2)))}
        for key, value in tests.items():
            self.assertTrue(encoder.output(encoder.state(key)).eq(tests[key]))
            self.assertTrue(tests[key].sort().eq(define.Output))

        fsm = define.MealyMachine()
        encoder = encode.MappingFSMEncoder(fsm)
        tests = {'a': fsm.output(encoder.state(''), define.input('a')),
                 'ab': fsm.output(encoder.state(('a',)), define.input('b')),
                 (1, 2): fsm.output(encoder.state('1'), define.input(2))}
        for key, value in tests.items():
            self.assertTrue(encoder.output(encoder.state(key[:-1]), define.input(key[-1])).eq(tests[key]))

    def test_states(self):
        # how can we properly test this at this level?
        # simply copying the code is cheating...
        # we might as well test this from a functional perspective in `learn'
        pass

    def test_outputs(self):
        # testing this would also be a matter of copying the code,
        # and is therefore not very useful.
        pass

    def test_node_iter(self):
        encoder = encode.MappingFSMEncoder(define.MooreMachine())
        encoder.state('ab')
        encoder.state('aa')

        nodes = {0, 1, 2, 3}
        for node in encoder._trie:
            self.assertTrue(node.id in nodes)

        transitions = {(0, 'a', 1), (1, 'b', 2), (1, 'a', 3)}
        for node, input, child in encoder._trie.transitions():
            self.assertTrue((node.id, input, child.id) in transitions)
