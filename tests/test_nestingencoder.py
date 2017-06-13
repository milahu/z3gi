from unittest import TestCase

from z3gi import define, encode


class TestNestingEncoder(TestCase):
    def test_state(self):
        for fsm in [define.MooreMachine(), define.MealyMachine()]:
            tests = {'': fsm.start,
                     'ab': fsm.transition(fsm.transition(fsm.start, define.input('a')), define.input('b')),
                     (1, 2): fsm.transition(fsm.transition(fsm.start, define.input(1)), define.input(2))}
            encoder = encode.NestingFSMEncoder(fsm)
            for key, value in tests.items():
                self.assertTrue(encoder.state(key).eq(tests[key]))

    def test_transition(self):
        for fsm in [define.MooreMachine(), define.MealyMachine()]:
            tests = {'ab': fsm.transition(fsm.transition(fsm.start, define.input('a')), define.input('b')),
                     (1, 2): fsm.transition(fsm.transition(fsm.start, define.input(1)), define.input(2))}
            encoder = encode.NestingFSMEncoder(fsm)
            for key, value in tests.items():
                self.assertTrue(encoder.transition(encoder.state(key[:-1]), define.input(key[-1])).eq(tests[key]))

    def test_output(self):
        fsm = define.MooreMachine()
        tests = {'': fsm.output(fsm.start),
                 'ab': fsm.output(fsm.transition(fsm.transition(fsm.start, define.input('a')), define.input('b'))),
                 (1, 2): fsm.output(fsm.transition(fsm.transition(fsm.start, define.input(1)), define.input(2)))}
        encoder = encode.NestingFSMEncoder(fsm)
        for key, value in tests.items():
            self.assertTrue(encoder.output(encoder.state(key)).eq(tests[key]))

        fsm = define.MealyMachine()
        tests = {'a': fsm.output(fsm.start, define.input('a')),
                 'ab': fsm.output(fsm.transition(fsm.start, define.input('a')), define.input('b')),
                 (1, 2): fsm.output(fsm.transition(fsm.start, define.input(1)), define.input(2))}
        encoder = encode.NestingFSMEncoder(fsm)
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
