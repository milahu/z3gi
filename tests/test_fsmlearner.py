from unittest import TestCase

import z3

from z3gi import define, encode, learn


class TestFSMLearner(TestCase):
    def test_add(self):
        fsm = define.MooreMachine()
        for encoder in [encode.NestingEncoder, encode.MappingEncoder]:
            learner = learn.FSMLearner(fsm, encoder)
            try:
                learner.add('', 0)
                learner.add('', '0')
                learner.add('abc', '0123')
                learner.add(['a', 'b', 'c'], (0, 1, 2, 3))
                learner.add('abc', 3)
            except (encode.EncodeError, learn.NonDeterminismError) as e:
                self.fail("Unexpected exception: {0}".format(e))

            with self.assertRaises(encode.EncodeError):
                learner.add('', '')
            with self.assertRaises(encode.EncodeError):
                learner.add('', '00')
            with self.assertRaises(encode.EncodeError):
                learner.add('a', '')
            with self.assertRaises(encode.EncodeError):
                learner.add(True, True)
            with self.assertRaises(learn.NonDeterminismError):
                learner.add('', 1)
            with self.assertRaises(learn.NonDeterminismError):
                learner.add('abc', '1123')

            self.assertEqual(learner.outputs, {'0', '1', '2', '3'})

        fsm = define.MealyMachine()
        for encoder in [encode.NestingEncoder, encode.MappingEncoder]:
            learner = learn.FSMLearner(fsm, encoder)
            try:
                learner.add('a', 0)
                learner.add('a', '0')
                learner.add('abc', '012')
                learner.add(['a', 'b', 'c'], (0, 1, 2))
                learner.add('abc', 2)
                learner.add('abc', '2')
            except (encode.EncodeError, learn.NonDeterminismError) as e:
                self.fail("Unexpected exception: {0}".format(e))

            with self.assertRaises(encode.EncodeError):
                learner.add('', '')
            with self.assertRaises(encode.EncodeError):
                learner.add('', '0')
            with self.assertRaises(encode.EncodeError):
                learner.add('a', '')
            with self.assertRaises(encode.EncodeError):
                learner.add(True, True)
            with self.assertRaises(learn.NonDeterminismError):
                learner.add('a', 1)
            with self.assertRaises(learn.NonDeterminismError):
                learner.add('abc', '022')

            self.assertEqual(learner.outputs, {'0', '1', '2'})

    def test_model(self):
        fsm = define.MooreMachine()
        for encoder in [encode.NestingEncoder, encode.MappingEncoder]:
            learner = learn.FSMLearner(fsm, encoder)
            learner.add('aaaa', '10010')
            with self.assertRaises(learn.LearnError):
                learner.model(max_states=2)
            model = learner.model()
            self.assertTrue(model.eval(z3.Int('n') == 3))
