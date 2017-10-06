from abc import ABCMeta, abstractmethod

from model import Automaton
from sut.simulation import MealyMachineSimulation
from test import TestGenerator, MealyTest
import parse.exporter
import subprocess
import os.path

class YannakakisTestGenerator(TestGenerator):

    def __init__(self, sut,
                 yan_path=os.path.join(os.path.dirname(__file__), "..", "..","resources", "binaries", "yannakakis.exe"),
                 mode="random", max_k=3, rand_length=3):
        self.yan_path = yan_path
        self.mode = mode
        self.max_k = max_k
        self.sut = sut
        self.r_length = rand_length
        self.yan_proc = None


    def initialize(self, model: Automaton):
        dot_content = parse.exporter.to_dot(model)
        #print(" ".join([self.yan_path, "=", self.mode, str(self.max_k), str(self.r_length)]))
        self.yan_proc = subprocess.Popen([self.yan_path, "=", self.mode, str(self.max_k), str(self.r_length)],
                                         stdin=subprocess.PIPE, stdout=subprocess.PIPE, bufsize=10, universal_newlines=True)
        self.yan_proc.stdin.write(dot_content)
        self.yan_proc.stdin.write("\n")
        self.yan_proc.stdin.flush()

    def gen_test(self, model: Automaton):
        if model is None:
            seq = self.gen_blind_inp_seq(self.sut)
            obs = self.sut.run(seq)
        else:
            test_string = self.yan_proc.stdout.readline()
            if test_string is None:
                return None
            inputs = test_string.split()
            obs = self.sut.run(inputs)
        test = MealyTest(obs.trace())
        return test

    def terminate(self):
        #os.remove("hyp.dot")
        self.yan_proc.terminate()
        self.yan_proc.wait()


