from model.fa import MutableMealyMachine, IOTransition
import model
import utils

__all__ =[
    "random_mealy"
]

def random_mealy(num_inputs:int, num_outputs:int, num_states:int, strongly_connected=True):
    inp_alpha = ["I" + str(i+1) for i in range(0, num_inputs)]
    out_alpha = ["O" + str(i+1) for i in range(0, num_outputs)]
    states = ["q" + str(i+1) for i in range(0, num_states)]

    while True:
        mm = MutableMealyMachine()
        for state in states:
            mm.add_state(state)

        for state in states:
            for inp in inp_alpha:
                r_out = utils.rand_sel(out_alpha)
                r_state = utils.rand_sel(states)
                tr = IOTransition(state, inp, r_out, r_state)
                mm.add_transition(state, tr)

        mm.generate_acc_seq()
        machine = mm.to_immutable()
        if len(machine.states()) == num_states:
            if not strongly_connected or model.is_strongly_connected(machine):
                return machine

