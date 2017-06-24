from unittest import TestCase
import z3
from z3gi_old import define


class TestDefine(TestCase):
    def test_state_type(self):
        self.assertTrue(define.State.eq(z3.DeclareSort('STATE')))

    def test_input_type(self):
        self.assertTrue(define.Input.eq(z3.DeclareSort('INPUT')))

    def test_output_type(self):
        self.assertTrue(define.Output.eq(z3.DeclareSort('OUTPUT')))

    def test_element_type(self):
        self.assertTrue(define.Element.eq(z3.DeclareSort('ELEMENT')))

    # ...
