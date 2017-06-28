import itertools

import z3

from define.ra import IORegisterAutomaton, Mapper
from encode import Encoder
from utils import Tree, determinize


class IORAEncoder(Encoder):
    def __init__(self):
        self.tree = Tree(itertools.count(0))
        self.values = set()
        self.input_labels = set()
        self.output_labels = set()

    def add(self, trace):
        seq = list(itertools.chain(*map(iter, trace)))
        _ = self.tree[determinize(seq)]
        self.values.update([action.value for action in seq])
        self.input_labels.update([action.label for action in [i for (i, o) in trace]])
        self.output_labels.update([action.label for action in [o for (i, o) in trace]])

    def build(self, num_locations, num_registers):
        ra = IORegisterAutomaton(list(self.input_labels), list(self.output_labels), num_locations, num_registers)
        mapper = Mapper(ra)
        constraints = []
        constraints.extend(self.axioms(ra, mapper))
        constraints.extend(self.node_constraints(ra, mapper))
        constraints.extend(self.transition_constraints(ra, mapper))
        return ra, constraints

    def axioms(self, ra: IORegisterAutomaton, mapper: Mapper):
        l, lp = z3.Consts('l lp', ra.Label)
        q, qp = z3.Consts('q qp', ra.Location)
        r, rp = z3.Consts('r rp', ra.Register)
        axioms = [
            # In the start state of the mapper,
            # all registers contain an uninitialized value.
            z3.ForAll(
                [r],
                mapper.valuation(mapper.start, r) == mapper.init
            ),

            # # If two locations are connected with both register and fresh transitions,
            # # then you have to do an update on a different register (otherwise you should merge the two transitions)
            z3.ForAll(
                [q, l, r],
                z3.Implies(
                    z3.And(
                        r != ra.fresh,
                        ra.transition(q, l, ra.fresh) == ra.transition(q, l, r),
                        ra.transition(q, l, ra.fresh) != ra.sink
                    ),
                    z3.And(
                        ra.update(q, l) != ra.fresh,
                        ra.update(q, l) != r
                    )
                )
            ),

            # The fresh register is never used
            z3.ForAll(
                [q],
                z3.Implies(
                    q != ra.sink,
                    ra.used(q, ra.fresh) == False
                )
            ),

            # If a variable is used after a transition, it means it was either used before, or it was assigned
            z3.ForAll(
                [q, l, r, rp],
                z3.Implies(
                    z3.And(
                        ra.used(ra.transition(q, l, rp), r) == True,
                        q != ra.sink
                    ),
                    z3.Or(
                        ra.used(q, r) == True,
                        z3.And(
                            ra.update(q, l) == r,
                            rp == ra.fresh
                        ),
                    )
                )
            ),

            # If a variable is updated, then it should have been used.
            z3.ForAll(
                [q, l, r],
                z3.Implies(
                    z3.And(
                        r != ra.fresh,
                        ra.update(q, l) == r,
                        q != ra.sink
                    ),
                    ra.used(ra.transition(q, l, ra.fresh), r) == True
                )
            ),

            # Registers are not used in the start state
            z3.ForAll(
                [r],
                ra.used(ra.start, r) == False
            )
        ]

        # # IO axioms
        axioms.extend([
            # The sink is labeled as an input location
            ra.loctype(ra.sink) == True,

            # Alternating input and output locations
            z3.ForAll(
                [q, l, r],
                z3.If(
                    ra.loctype(q) == True,
                    z3.Or(
                        ra.loctype(ra.transition(q, l, r)) == False,
                        ra.transition(q, l, r) == ra.sink
                    ),
                    ra.loctype(ra.transition(q, l, r)) == True
                )
            ),

            # The sink is the only rejecting state
            z3.ForAll(
                [q],
                z3.If(
                    q == ra.sink,
                    ra.output(q) == False,
                    ra.output(q) == True
                )
            ),

            # The start location is an input location
            ra.loctype(ra.start) == True,

            # In output locations, there's only one transition possible
            z3.ForAll(
                [q, l, lp, r, rp],
                z3.Implies(
                    z3.And(
                        q != ra.sink,
                        ra.loctype(q) == False,
                        ra.transition(q, l, r) != ra.sink,
                        z3.Or(
                            r != rp,
                            l != lp
                        )
                    ),
                    ra.transition(q, lp, rp) == ra.sink
                )
            ),

            # The sink is a sink
            z3.ForAll(
                [l, r],
                ra.transition(ra.sink, l, r) == ra.sink
            ),

            # The sink doesn't update registers
            z3.ForAll(
                [l],
                ra.update(ra.sink, l) == ra.fresh
            )
        ])

        # From input locations, all output transitions go to sink.
        axioms.extend([
            z3.ForAll(
                [q, r],
                z3.Implies(
                    ra.loctype(q) == True,
                    ra.transition(q, ra.labels[l], r) == ra.sink
                )
            )
        for l in self.output_labels])

        # From output locations, all input transitions go to sink.
        axioms.extend([
            z3.ForAll(
                [q, r],
                z3.Implies(
                    ra.loctype(q) == False,
                    ra.transition(q, ra. labels[l], r) == ra.sink
                )
            )
        for l in self.input_labels])

        # # Input enabled
        # axioms.extend([
        #     z3.ForAll(
        #         [q, r],
        #         z3.Implies(
        #             z3.And(
        #                 ra.loctype(q) == True,
        #                 q != ra.sink
        #             ),
        #             ra.transition(q, ra.labels[l], r) != ra.sink
        #         )
        #     )
        # for l in self.input_labels])

        return axioms

    def node_constraints(self, ra, mapper):
        constraints = []
        for node in self.tree:
            n = mapper.element(node.id)
            constraints.append(mapper.map(n) != ra.sink)

        return constraints

    def transition_constraints(self, ra, mapper):
        constraints = [ra.start == mapper.map(mapper.start), ra.sink != ra.start]
        values = {mapper.init}
        for node, (label, value), child in self.tree.transitions():
            n = mapper.element(node.id)
            l = ra.labels[label]
            v = mapper.value(value)
            c = mapper.element(child.id)
            r, rp = z3.Consts('r rp', ra.Register)

            constraints.extend([
                # If the transition is over a register, then the register is in use.
                z3.ForAll(
                    [r],
                    z3.Implies(
                        z3.And(
                            r != ra.fresh,
                            ra.transition(mapper.map(n), l, r) == mapper.map(c)
                        ),
                        ra.used(mapper.map(n), r) == True
                    )
                ),

                # If a non-fresh register has changed, it must have been updated
                z3.ForAll(
                    [r],
                    z3.Implies(
                        z3.And(
                            r != ra.fresh,
                            mapper.valuation(c, r) != mapper.valuation(n, r)
                        ),
                        ra.update(mapper.map(n), l) == r
                    )
                ),

                # If a used, non-fresh register keeps its value, then it was not updated.
                z3.ForAll(
                    [r],
                    z3.Implies(
                        z3.And(
                            r != ra.fresh,
                            mapper.valuation(c, r) == mapper.valuation(n, r),
                            ra.used(mapper.map(n), r) == True
                        ),
                        ra.update(mapper.map(n), l) != r
                    )
                ),

                # If a non-fresh register is updated, and c and n are connect by fresh,
                # then in c there is a register whose value is v,
                # else the valuation is maintained.
                z3.ForAll(
                    [r],
                    z3.If(
                        z3.And(
                            r != ra.fresh,
                            ra.update(mapper.map(n), l) == r,
                            ra.transition(mapper.map(n), l, ra.fresh) == mapper.map(c)
                        ),
                        z3.Exists(
                            [rp],
                            z3.And(
                                rp != ra.fresh,
                                mapper.valuation(c, rp) == v
                            )
                        ),
                        mapper.valuation(c, r) == mapper.valuation(n, r)
                    )
                )
            ])

            # Map to the right transition
            path = [v for (l, v) in node.path()]
            print(path)
            if value in path:
                if label in self.input_labels:
                    constraints.append(
                        z3.If(
                            z3.Exists(
                                [r],
                                z3.And(
                                    r != ra.fresh,
                                    mapper.valuation(n, r) == v
                                )
                            ),
                            z3.ForAll(
                                [r],
                                z3.Implies(
                                    z3.And(
                                        r != ra.fresh,
                                        mapper.valuation(n, r) == v
                                    ),
                                    z3.If(
                                        ra.used(mapper.map(n), r) == True,
                                        # it might not keep the valuation
                                        ra.transition(mapper.map(n), l, r) == mapper.map(c),
                                        ra.transition(mapper.map(n), l, ra.fresh) == mapper.map(c)
                                    )
                                )
                            ),
                            ra.transition(mapper.map(n), l, ra.fresh) == mapper.map(c)
                        )
                    )
                elif label in self.output_labels:
                    constraints.append(
                        z3.If(
                            z3.Exists(
                                [r],
                                z3.And(
                                    r != ra.fresh,
                                    mapper.valuation(n, r) == v
                                )
                            ),
                            z3.ForAll(
                                [r],
                                z3.Implies(
                                    z3.And(
                                        r != ra.fresh,
                                        mapper.valuation(n, r) == v
                                    ),
                                    z3.And(
                                        ra.used(mapper.map(n), r) == True,
                                        ra.transition(mapper.map(n), l, r) == mapper.map(c),
                                    )
                                )
                            ),
                            False
                        )
                    )
                else:
                    raise Exception("We did something wrong")

            else:
                # Take the fresh transition
                constraints.append(ra.transition(mapper.map(n), l, ra.fresh) == mapper.map(c))

                # # Map to the right transition
                # z3.If(
                #     z3.Exists(
                #         [r],
                #         z3.And(
                #             r != ra.fresh,
                #             mapper.valuation(n, r) == v
                #         )
                #     ),
                #     z3.ForAll(
                #         [r],
                #         z3.Implies(
                #             z3.And(
                #                 r != ra.fresh,
                #                 mapper.valuation(n, r) == v
                #             ),
                #             z3.If(
                #                 ra.used(mapper.map(n), r) == True,
                #                 # it might not keep the valuation
                #                 ra.transition(mapper.map(n), l, r) == mapper.map(c),
                #                 ra.transition(mapper.map(n), l, ra.fresh) == mapper.map(c)
                #             )
                #         )
                #     ),
                #     ra.transition(mapper.map(n), l, ra.fresh) == mapper.map(c)
                # )


            values.add(v)

        constraints.append(z3.Distinct(list(values)))
        # Do we need to make labels distinct as well?

        return constraints
