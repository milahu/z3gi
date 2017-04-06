import io
import unittest

from z3gi.encoders import natural

class TestNaturalEncoder(unittest.TestCase):

    def test_NonDeterminsimError(self):
        encoder = natural.Encoder()
        encoder['a'] = True
        with self.assertRaises(natural.NonDeterminismError):
            encoder['a'] = False

    def test_default_settings(self):
        encoder = natural.Encoder()
        encoder['a'] = True
        self.assertEqual(len(encoder.encode(1)), 4)

    def test_inequalities_setting(self):
        encoder = natural.Encoder(inequalities=True)
        encoder['a'] = True
        self.assertEqual(len(encoder.encode(2)), 5)

    def test_no_quantifiers_setting(self):
        encoder = natural.Encoder(quantifiers=False)
        encoder['a'] = True
        self.assertEqual(len(encoder.encode(1)), 4)

if __name__ == '__main__':
    unittest.main()
