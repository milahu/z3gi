from unittest import TestCase

import z3

from z3gi import define, encode

fsms = [define.MooreMachine(), define.MealyMachine()]


# We're only testing type safety here, not the actual implementation
class TestFSMEncoder(TestCase):
    def test_state(self):
        for fsm in fsms:
            encoder = encode.NestingEncoder(fsm)
            try:
                self.assertTrue(encoder.state('').sort().eq(define.State))
                self.assertTrue(encoder.state((1, 2, 3)).sort().eq(define.State))
                self.assertTrue(encoder.state([i for i in range(5)]).sort().eq(define.State))
                self.assertTrue(encoder.state('').eq(encoder.state([])))
            except encode.EncodeError:
                self.fail()
            with self.assertRaises(encode.EncodeError):
                encoder.state(1)
            with self.assertRaises(encode.EncodeError):
                encoder.state(True)

    def test_transition(self):
        for fsm in fsms:
            encoder = encode.NestingEncoder(fsm)
            try:
                self.assertTrue(encoder.transition(encoder.state('abc'), define.input()).sort().eq(define.State))
                self.assertTrue(encoder.transition(define.state(), define.input()).sort().eq(define.State))
            except encode.EncodeError:
                self.fail()
            with self.assertRaises(encode.EncodeError):
                encoder.transition('state', 'input')
            with self.assertRaises(encode.EncodeError):
                encoder.transition(None, None)

    def test_output(self):
        encoder = encode.NestingEncoder(define.MooreMachine())
        try:
            self.assertTrue(encoder.output(encoder.state('abc')).sort().eq(define.Output))
            self.assertTrue(encoder.output(define.state()).sort().eq(define.Output))
        except encode.EncodeError:
            self.fail()
        with self.assertRaises(encode.EncodeError):
            encoder.output('state')
        with self.assertRaises(encode.EncodeError):
            encoder.output(None)
        with self.assertRaises(encode.EncodeError):
            encoder.output(define.state(), define.input())

        encoder = encode.NestingEncoder(define.MealyMachine())
        try:
            self.assertTrue(encoder.output(encoder.state('abc'), define.input()).sort().eq(define.Output))
            self.assertTrue(encoder.output(define.state(), define.input()).sort().eq(define.Output))
        except encode.EncodeError:
            self.fail()
        with self.assertRaises(encode.EncodeError):
            encoder.output('state', 'input')
        with self.assertRaises(encode.EncodeError):
            encoder.output(None)
        with self.assertRaises(encode.EncodeError):
            encoder.output(define.state())

    def test_states(self):
        for fsm in fsms:
            encoder = encode.NestingEncoder(fsm)
            try:
                self.assertTrue(encoder.states(range(10)).sort().eq(z3.BoolSort()))
                self.assertTrue(encoder.states(['a']).sort().eq(z3.BoolSort()))
            except encode.EncodeError:
                self.fail()

            with self.assertRaises(encode.EncodeError):
                encoder.states([])
            with self.assertRaises(encode.EncodeError):
                encoder.states(1)

    def test_outputs(self):
        for fsm in fsms:
            encoder = encode.NestingEncoder(fsm)
            try:
                self.assertTrue(encoder.outputs(range(10)).sort().eq(z3.BoolSort()))
                self.assertTrue(encoder.outputs(['a']).sort().eq(z3.BoolSort()))
                self.assertTrue(encoder.outputs('ab').sort().eq(z3.BoolSort()))
                self.assertTrue(encoder.outputs({'a', 'b', 1}).sort().eq(z3.BoolSort()))
            except encode.EncodeError:
                self.fail()

            with self.assertRaises(encode.EncodeError):
                encoder.outputs([])
            with self.assertRaises(encode.EncodeError):
                encoder.outputs(1)
