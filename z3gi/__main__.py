"""A client module for using the z3gi from the command line."""
import argparse

import learn.algorithm as alg
import parse.importer as parse
import sut
import model.fa
import model.gen as gen

from encode.fa import MealyEncoder, DFAEncoder
from encode.iora import IORAEncoder
from encode.ra import RAEncoder
from learn.fa import FALearner
from learn.ra import RALearner
from test import AcceptorTest, IORATest, MealyTest

from test.rwalk import RARWalkFromState
from test.rwalk import IORARWalkFromState
from test.rwalk import MealyRWalkFromState
from test.rwalk import DFARWalkFromState
from test.yanna import YannakakisTestGenerator

"""some configuration mappings"""
aut2learner={
    model.ra.RegisterAutomaton:RALearner(RAEncoder()),
    model.ra.IORegisterAutomaton:RALearner(IORAEncoder()),
    model.fa.MealyMachine:FALearner(MealyEncoder()),
    model.fa.DFA:FALearner(DFAEncoder())
}

aut2rwalkcls={
    model.ra.RegisterAutomaton:RARWalkFromState,
    model.ra.IORegisterAutomaton:IORARWalkFromState,
    model.fa.MealyMachine:MealyRWalkFromState,
    model.fa.DFA:DFARWalkFromState
}

aut2testcls={
    model.ra.RegisterAutomaton:AcceptorTest,
    model.ra.IORegisterAutomaton:IORATest,
    model.fa.MealyMachine:MealyTest,
    model.fa.DFA:AcceptorTest
}

aut2suttype={
    model.ra.RegisterAutomaton: sut.SUTType.RA,
    model.ra.IORegisterAutomaton: sut.SUTType.IORA,
    model.fa.MealyMachine:sut.SUTType.Mealy,
    model.fa.DFA:sut.SUTType.DFA
}

# the interface is a bit convoluted, but it does give access to all the functionality available
if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Inference tool which can:\n'
                                                 '(1) passively learn from traces file\n'
                                                 '(2) actively learn a Mealy Machine system described by a .dot file\n'
                                                 '(3) actively learn a Mealy Machine system described by a .dot file without resets\n'
                                                 '(4) actively learn a randomly generated Mealy Machine without resets\n'
                                                 '(5) actively learn a scalable SUT (system) of a given size')
    parser.add_argument('-m', '--mode', type=str, choices=['traces', 'dot', 'dotnorst','randnorst', 'scalable'], required=True)
    parser.add_argument('-f', '--file', type=str, help='the file location to the dot/traces file')
    parser.add_argument('-a', '--aut', type=str, choices=list(model.defined_formalisms().keys()), required=True,
                        help='the type of automaton (formalism) described in the file or '
                                                       'which characterizes the (scalable) SUT')
    parser.add_argument('-sc', '--sut_class', type=str, choices=list(sut.scalable_sut_classes().keys()),
                        help='the class of the scalable SUT')
    parser.add_argument('-s', '--size', type=int, help='the size of the scalable SUT')
    parser.add_argument('-t', '--timeout', type=int, help='the timeout used in learning '
                                                          '(i.e. the time limit given to the solver to solve the constraints)')
    parser.add_argument('-ni', '--num-inputs', type=int, default=2, help='the input alphabet size of the random Mealy machine')
    parser.add_argument('-no', '--num-outputs', type=int, default=2,
                        help='the output alphabet size of the random Mealy machine')
    parser.add_argument('-ns', '--num-states', type=int, default=10,
                        help='the number of states of the random Mealy machine')

    # test parameters
    parser.add_argument('-mi', '--max_inputs', type=int, default=1000, help='the max number of inputs executed on a '
                                                                          'hypothesis before it is judged to be correct, '
                                                                          'only considered for learning with no resets')
    parser.add_argument('-mt', '--max_tests', type=int, default=1000, help='the max number of tests executed on a '
                                                                           'hypothesis before it is judged to be correct')
    parser.add_argument('-rl', '--rand_length', type=int, default=5, help='the maximum length of the random sequence '
                                                                          ' used by rwalkfromstate')
    parser.add_argument('-rp', '--reset_prob', type=float, default=0.2, help='the probability of reseting the SUT after '
                                                                            'running each test input')
    parser.add_argument('-y', '--yannakakis', type=str, default=None, help='uses the yannakakis instead of rwalkfromstate '
                                                                        '(only supports Mealy Machines).'
                                                                           ' Takes the path to the yannakakis binary as argument.')

    args = parser.parse_args()
    formalism = args.aut
    formalisms = model.defined_formalisms()
    aut_type = formalisms[formalism]

    learner = aut2learner[aut_type]

    if args.mode == 'traces':
        trace_file = args.file
        traces = parse.extract_traces_from_file(args.file, formalism)
        print(traces)
        (automaton, statistics) = alg.learn(learner, aut2testcls[aut_type], traces)
    else:
        if args.mode == 'dotnorst':
            dot_file = args.file
            aut_to_learn = parse.build_automaton_from_dot(formalism, dot_file)
            sut_to_learn = sut.get_no_rst_simulation(aut_to_learn)
            max_inputs = args.max_inputs
            (automaton, statistics) = alg.learn_no_reset(sut_to_learn, learner, max_inputs)
        elif args.mode == 'randnorst':
            ni = args.num_inputs
            no = args.num_inputs
            ns = args.num_states
            aut_to_learn = gen.random_mealy(ni, no, ns)
            sut_to_learn = sut.get_no_rst_simulation(aut_to_learn)
            max_inputs = args.max_inputs
            (automaton, statistics) = alg.learn_no_reset(sut_to_learn, learner, max_inputs)
        else:
            if args.mode == 'dot':
                dot_file = args.file
                aut_to_learn = parse.build_automaton_from_dot(formalism, dot_file)
                sut_to_learn = sut.get_simulation(aut_to_learn)
            elif args.mode == 'scalable':
                sut_class_name = args.sut_class
                sut_size = args.size
                sut_to_learn = sut.get_scalable_sut(sut_class_name, aut2suttype[aut_type], sut_size)
            else:
                print("Invalid mode ", args.mode)
                exit(1)

            num_tests = args.max_tests
            rand_test_length = args.rand_length
            reset_prob = args.reset_prob
            if args.yannakakis is None:
                test_generator = aut2rwalkcls[aut_type](sut_to_learn, rand_test_length, reset_prob)
            else:
                test_generator = YannakakisTestGenerator(sut_to_learn, args.yannakakis, rand_length=rand_test_length)
            (automaton, statistics) = alg.learn_mbt(sut_to_learn, learner, test_generator, num_tests)

    print("Learned model\n", automaton, "\nWith stats\n", statistics)