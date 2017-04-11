"""A standalone for using the z3gi package from the command line."""
import sys
import argparse

from z3gi.sample import Sample
from z3gi.parsers import abbadingo
from z3gi.encoders import propositional
from z3gi.encoders import natural
from z3gi.encoders import expressive
from z3gi.encoders import mealy

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Find a minimal encoding for a sample of labeled abbadingo strings.')
    parser.add_argument('-f', '--file', help='run on abbadingo file and exit')
    parser.add_argument('-m', '--model', action='store_true', help='print learned model to stdout')
    parser.add_argument('-s', '--statistics', action='store_true', help='print z3 statistics to stdout')
    parser.add_argument('--natural', action='store_true', help='use natural encoding (default)')
    parser.add_argument('--expressive', action='store_true', help='use expressive encoding')
    parser.add_argument('--propositional', action='store_true', help='use propositional encoding (dfasat)')
    parser.add_argument('--mealy', action='store_true', help='use mealy encoding')
    parser.add_argument('-nq', '--no_quantifiers', dest='quantifiers', action='store_false', help="do not use z3's quantifiers in theory solver")
    parser.add_argument('-in', '--inequalities', action='store_true', help='use inequalities in theory solver')
    parser.add_argument('-re', '--redundant', action='store_true', help='use redundant constaints (only applies for propositional encoding)')

    args = parser.parse_args()

    encoder = natural.Encoder(args.quantifiers, args.inequalities)
    if args.propositional:
        encoder = propositional.Encoder(args.redundant)
    elif args.mealy:
        encoder = mealy.Encoder(args.quantifiers, args.inequalities)
    elif args.expressive:
        encoder = expressive.Encoder(args.quantifiers, args.inequalities)

    sample = Sample(encoder)

    f = sys.stdin
    header = 0
    if args.file:
        f = open(args.file, 'r')
        header = 1

    for string, label in abbadingo.read(f, header):
        sample[string] = label

    model = sample.model()

    if args.model:
        print("Learned model:")
        print(model)
    if args.statistics:
        print("Z3 statistics:")
        print(sample.statistics)
