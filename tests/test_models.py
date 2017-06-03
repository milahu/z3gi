import io
import unittest

from z3gi.models import dfa
from z3gi.sample import Sample

class TestDFA(unittest.TestCase):
    def setUp(self):
        self.sample = Sample()
        self.sample['a'] = True
        self.sample['aa'] = False
        self.model = self.sample.model()

    def test_start(self):
        start = self.model._statemap[self.model.model.evaluate(self.model._start)]
        self.assertEqual(self.model.state(''), start)

    def test_state(self):
        self.assertNotEqual(self.model.state('a'), self.model.state('aa'))

    def test_accepting(self):
        self.assertNotEqual(self.model.is_accepting(self.model.state('a')), self.model.is_accepting(self.model.state('aa')))

    def test_transition(self):
        self.assertEqual(self.model.state('aa'), self.model.transition(self.model.state('a'), 'a'))

    def test_export(self):
        self.model.export()
        pass

if __name__ == '__main__':
    unittest.main()
