from model import Automaton
from test import TestGenerator, MealyTest
import parse.exporter
import subprocess
import os.path

class YannakakisTestGenerator(TestGenerator):

    def __init__(self, sut,
                 yan_path=os.path.join(os.path.dirname(__file__), "..", "..","resources", "binaries", "yannakakis.exe"),
                 mode="random", max_k=1, rand_length=1, seed=None):
        self.yan_path = yan_path
        self.mode = mode
        self.max_k = max_k
        self.sut = sut
        self.r_length = rand_length
        self.yan_proc = None
        self.seed = seed


    def initialize(self, model: Automaton):
        dot_content = parse.exporter.to_dot(model)
        yan_cmd = [self.yan_path, "=", self.mode, str(self.max_k), str(self.r_length)]
        if self.seed is not None:
            yan_cmd.extend(["--seed", str(self.seed)])
        self.yan_proc = subprocess.Popen(yan_cmd,
                                         stdin=subprocess.PIPE, stdout=subprocess.PIPE, bufsize=10, universal_newlines=True)
        self.yan_proc.stdin.write(dot_content)
        self.yan_proc.stdin.write("\n")
        self.yan_proc.stdin.flush()
        #self.yan_proc = subprocess.Popen([self.yan_path, os.path.join("..", "resources", "models","bankcards", "VISA.dot"),
        #                                 "fixed", "1", "1"],
        #                                stdin=subprocess.PIPE, stdout=subprocess.PIPE, bufsize=10, universal_newlines=True)

    def gen_test(self, model: Automaton):
        test_string = self.yan_proc.stdout.readline()
        if test_string is None:
            return None
        inputs = test_string.split()
        obs = self.sut.run(inputs)
        test = MealyTest(obs.trace())
        return test

    def terminate(self):
        self.yan_proc.terminate()
        self.yan_proc.wait()


