from encode.iora import IORAEncoder
from learn.algorithm import learn
from learn.ra import RALearner
from sut.login import new_login_sut
from sut.stack import new_stack_sut
from sut.fifoset import new_fifoset_sut
from test import IORATest
from test.generation import ExhaustiveRAGenerator

# stack_sut = new_stack_sut(2)
# gen = ExhaustiveRAGenerator(stack_sut)
# obs = gen.generate_observations(4, max_registers=2)
# print("\n".join( [str(obs) for obs in obs]))
# learner = RALearner(IORAEncoder())
# (model, stats) = learn(learner, IORATest, obs)
# print(model, "\n \n", stats)

# set_sut = new_fifoset_sut(2)
# gen = ExhaustiveRAGenerator(set_sut)
# obs = gen.generate_observations(6, max_registers=2)
# print("\n".join( [str(obs) for obs in obs]))
# learner = RALearner(IORAEncoder())
# (model, stats) = learn(learner, IORATest, obs)
# print(model, "\n \n", stats)

login_sut = new_login_sut(2)
gen = ExhaustiveRAGenerator(login_sut)
obs = gen.generate_observations(8, max_registers=2)
print("\n".join( [str(obs) for obs in obs]))
learner = RALearner(IORAEncoder())
(model, stats) = learn(learner, IORATest, obs)
print(model, "\n \n", stats)