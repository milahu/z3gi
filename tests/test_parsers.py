import io
import unittest

from z3gi.parsers import abbadingo

class TestAbbadingoParser(unittest.TestCase):

    def test_read_labeled_string(self):
        f = io.StringIO('1 2 a b')
        for string, label in abbadingo.read(f):
            self.assertEqual(string, ['a', 'b'])
            self.assertEqual(label, True)

    def test_parse_labeled_string(self):
        line = '1 2 a b'
        self.assertEqual(abbadingo.parse(line), (['a', 'b'], True))

    def test_read_trace(self):
        f = io.StringIO('1 2 a/0 b/1')
        for inputs, outputs in abbadingo.read(f):
            self.assertEqual(inputs, ['a', 'b'])
            self.assertEqual(outputs, ['0', '1'])

    def test_parse_labeled_string(self):
        line = '1 2 a/0 b/1'
        self.assertEqual(abbadingo.parse(line), (['a', 'b'], ['0', '1']))

    def test_read_header(self):
        f = io.StringIO('0 0')
        for _ in abbadingo.read(f, header=1):
            self.fail("A line is read from an empty file")

if __name__ == '__main__':
    unittest.main()
