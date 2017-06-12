from unittest import TestCase
import z3
from z3gi import define


class TestDefine(TestCase):
    def test_state_type(self):
        self.assertTrue(define.STATE.eq(z3.DeclareSort('STATE')))

    def test_input_type(self):
        self.assertTrue(define.INPUT.eq(z3.DeclareSort('INPUT')))

    def test_output_type(self):
        self.assertTrue(define.OUTPUT.eq(z3.DeclareSort('OUTPUT')))

    def test_element_type(self):
        self.assertTrue(define.ELEMENT.eq(z3.DeclareSort('ELEMENT')))

    # ...
