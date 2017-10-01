import itertools

import z3
from encode import Encoder
from define.ra import IORegisterAutomaton2, Mapper
from utils import Tree, determinize


class IORA2Encoder(Encoder):
    def __init__(self):
        self.tree = Tree(itertools.count(0))
        self.values = set()
        self.inputs = set()
        self.outputs = set()

    def add(self, trace):
        flat = determinize(list(itertools.chain(*map(iter, trace))))
        trace = [(flat[i], flat[i+1]) for i in range(0, len(flat), 2)]
        _ = self.tree[trace]
        self.values.update([action.value for action in flat])
        self.inputs.update([action.label for action in [i for (i, o) in trace]])
        self.outputs.update([action.label for action in [o for (i, o) in trace]])

    def build(self, num_locations, num_registers) -> (IORegisterAutomaton2, z3.ExprRef):
        ra = IORegisterAutomaton2(list(self.inputs), list(self.outputs), num_locations, num_registers)
        mapper = Mapper(ra)
        constraints = self.axioms(ra, mapper) + \
                      self.node_constraints(ra, mapper) + \
                      self.transition_constraints(ra, mapper)
        return ra, constraints

    def axioms(self, ra: IORegisterAutomaton2, mapper: Mapper):
        i = z3.Const('i', ra.Input)
        o = z3.Const('o', ra.Output)
        q, qp = z3.Consts('q qp', ra.Location)
        r, rp = z3.Consts('r rp', ra.Register)
        axioms = [
            # In the start state of the mapper,
            # all registers contain an uninitialized value.
            # axiom not needed
            z3.ForAll(
                [r],
                mapper.valuation(mapper.start, r) == mapper.init
            ),

            # The fresh register is never used
            z3.ForAll(
                [q],
                ra.used(q, ra.fresh) == False
            ),

            # If a variable is used after a transition, it means it was either used before, or it was assigned
            z3.ForAll(
                [q, i, r, rp],
                z3.Implies(
                    ra.used(ra.transition(q, i, rp), r) == True,
                    z3.Or(
                        ra.used(q, r) == True,
                        z3.And(
                            ra.update(q, i) == r,
                            rp == ra.fresh
                        ),
                    )
                )
            ),

            # If a registers is updated, then it is used afterwards.
            z3.ForAll(
                [q, i, r],
                z3.Implies(
                    z3.And(
                        r != ra.fresh,
                        ra.update(q, i) == r
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

        return axioms

    def node_constraints(self, ra, mapper):
        return []

    def transition_constraints(self, ra, mapper):
        constraints = [ra.start == mapper.map(mapper.start)]
        values = {mapper.init}
        for node, ((input, val_in), (output, val_out)), child in self.tree.transitions():
            n = mapper.element(node.id)
            i = ra.inputs[input]
            o = ra.ouptuts[output]
            vi = mapper.value(val_in)
            vo = mapper.value(val_out)
            c = mapper.element(child.id)
            r, rp = z3.Consts('r rp', ra.Register)

            values.add(vi)
            values.add(vo)

            constraints.extend([
                # If the transition is over a register, then the register is in use.
                # z3.ForAll(
                #     [r],
                #     z3.Implies(
                #         z3.And(
                #             r!= ra.fresh,
                #             ra.transition(mapper.map(n), l, r) == mapper.map(c)
                #         ),
                #         ra.used(mapper.map(n), r) == True
                #     )
                # ),

                # If a non-fresh register has changed, it must have been updated
                z3.ForAll(
                    [r],
                    z3.Implies(
                        z3.And(
                            r != ra.fresh,
                            mapper.valuation(c, r) != mapper.valuation(n, r)
                        ),
                        ra.update(mapper.map(n), i) == r
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
                        ra.update(mapper.map(n), i) != r
                    )
                ),

                # If a non-fresh register is updated, and c and n are connected by fresh,
                # then the register contains the value
                # else the valuation is maintained.
                z3.ForAll(
                    [r],
                    z3.If(
                        z3.And(
                            r != ra.fresh,
                            ra.update(mapper.map(n), i) == r,
                            ra.transition(mapper.map(n), i, ra.fresh) == mapper.map(c)
                        ),
                        mapper.valuation(c, r) == vi,
                        mapper.valuation(c, r) == mapper.valuation(n, r)
                    )
                ),
            ])

            path = [v for (l, v) in node.path()]

            # Map to the right transition
            if val_in in path:
                constraints.append(
                    z3.If(
                        z3.Exists(
                            [r],
                            z3.And(
                                r != ra.fresh,
                                mapper.valuation(n, r) == vi,
                                ra.used(mapper.map(n), r) == True
                            )
                        ),
                        z3.ForAll(
                            [r],
                            z3.Implies(
                                z3.And(
                                    r != ra.fresh,
                                    mapper.valuation(n, r) == vi,
                                    ra.used(mapper.map(n), r) == True
                                ),
                                ra.transition(mapper.map(n), i, r) == mapper.map(c)
                            )
                        ),
                        ra.transition(mapper.map(n), i, ra.fresh) == mapper.map(c)
                    )
                )
            else:
                constraints.append(
                    ra.transition(mapper.map(n), i, ra.fresh) == mapper.map(c)
                )

            # TODO: output constraints need to be nested in the constraints here above
            # (and they need to be set at the same time as transition)

        constraints.append(z3.Distinct(list(values)))
        return constraints
