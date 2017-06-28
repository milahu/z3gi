import itertools
import z3

from encode.ra import RAEncoder, determinize
from define.ra import IORegisterAutomaton

class IORAEncoder(RAEncoder):

    def __init__(self):
        super().__init__()
        del self.cache
        self.inputs = set()
        self.outputs = set()

    def add(self, trace):
        seq = list(itertools.chain(*map(iter, trace)))
        print(list(seq))
        node = self.tree[determinize(seq)]
        self.values.update([action.value for action in seq])
        self.inputs.update([action.label for action in [i for (i, o) in trace]])
        self.outputs.update([action.label for action in [o for (i, o) in trace]])

    def build(self, iora: IORegisterAutomaton, initialized=True):
        mapper = IORAEncoder.Mapper(iora)
        return self.axioms(iora, mapper, initialized) + self.transition_constraints(iora, mapper) + self.io_axioms(iora)

    def io_axioms(self, iora):
        l, lp = z3.Consts('l lp', iora.Label)
        q, qp = z3.Consts('q qp', iora.Location)
        r, rp = z3.Consts('r rp', iora.Register)
        axioms = [
            # The start state is an input location
            iora.statetype(iora.start) == True,

            # All false guards go to sink, and al true guards don't go to sink
            z3.ForAll(
                [q, l, r],
                z3.Implies(
                    z3.And(
                        iora.guard(q, l, r) == True,
                        q != iora.sink
                    ),
                    iora.transition(q, l, r) != iora.sink
                )
            ),

            # Alternating input and output locations
            z3.ForAll(
                [q, l, r],
                z3.Implies(
                    z3.And(
                        q != iora.sink,
                        iora.guard(q, l, r) == True
                    ),
                    z3.If(
                        iora.statetype(q) == True,
                        iora.statetype(iora.transition(q, l, r)) == False,
                        iora.statetype(iora.transition(q, l, r)) == True
                    )
                )
            ),

            # In output locations, there's only one possible transition
            z3.ForAll(
                [q, l, r],
                z3.Implies(
                    z3.And(
                        q != iora.sink,
                        iora.statetype(q) == False,
                        iora.guard(q, l, r) == True
                    ),
                    z3.ForAll(
                        [lp, rp],
                        z3.Implies(
                            z3.And(
                                lp != l,
                                rp != r
                            ),
                            z3.And(
                                iora.guard(q, lp, rp) == False,
                                iora.transition(q, lp, rp) == iora.sink
                            )
                        )
                    )
                )
            ),

            # The sink is a sink :)
            z3.ForAll(
                [l, r],
                iora.transition(iora.sink, l, r) == iora.sink
            )
        ]

        # From input locations, disable all guards for output labels (and vise versa)
        inputs = [iora.labels[i] for i in self.inputs]
        outputs = [iora.labels[o] for o in self.outputs]
        axioms.extend(
            [z3.ForAll(
                [q, r],
                z3.Implies(
                    z3.And(
                        iora.statetype(q) == True,
                        r != iora.fresh
                    ),
                    iora.guard(q, lo, r) == False
                )
            ) for lo in outputs]
        )
        axioms.extend(
            [z3.ForAll(
                [q, r],
                z3.Implies(
                    z3.And(
                        iora.statetype(q) == False,
                        r != iora.fresh
                    ),
                    iora.guard(q, li, r) == False
                )
            ) for li in inputs]
        )

        return axioms