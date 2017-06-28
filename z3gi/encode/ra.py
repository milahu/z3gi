import itertools
import z3

from encode import Encoder
from define.ra import RegisterAutomaton, Mapper
from utils import Tree, determinize


class RAEncoder(Encoder):
    def __init__(self):
        self.tree = Tree(itertools.count(0))
        self.cache = {}
        self.values = set()
        self.labels = set()

    def add(self, trace):
        seq, accept = trace
        node = self.tree[determinize(seq)]
        self.cache[node] = accept
        self.values.update([action.value for action in seq])
        self.labels.update([action.label for action in seq])

    def build(self, num_locations, num_registers):
        ra = RegisterAutomaton(list(self.labels), num_locations, num_registers)
        mapper = Mapper(ra)
        constraints = self.axioms(ra, mapper) + \
                      self.output_constraints(ra, mapper) + \
                      self.transition_constraints(ra, mapper)
        return ra, constraints


    @staticmethod
    def axioms(ra : RegisterAutomaton, mapper):
        l = z3.Const('l', ra.Label)
        q, qp = z3.Consts('q qp', ra.Location)
        r, rp = z3.Consts('r rp', ra.Register)
        axioms = [
            # In the start state of the mapper,
            # all registers contain an uninitialized value.
            z3.ForAll(
                [r],
                mapper.valuation(mapper.start, r) == mapper.init
            ),

            # If two locations are connected with both register and fresh transitions,
            # then you have to do an update on a different register (otherwise you should merge the two transitions)
            z3.ForAll(
                [q, l, r],
                z3.Implies(
                    z3.And(
                        r != ra.fresh,
                        ra.transition(q, l, ra.fresh) == ra.transition(q, l, r),
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
                ra.used(q, ra.fresh) == False
            ),

            # If a variable is used after a transition, it means it was either used before, or it was assigned
            z3.ForAll(
                [q, l, r, rp],
                z3.Implies(
                    ra.used(ra.transition(q, l, rp), r) == True,
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
                        ra.update(q, l) == r
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

    def output_constraints(self, ra, mapper):
        constraints = []
        for node, accept in self.cache.items():
            n = mapper.element(node.id)
            constraints.extend(
                [ra.output(mapper.map(n)) == accept]
            )

        return constraints

    def transition_constraints(self, ra, mapper):
        constraints = [ra.start == mapper.map(mapper.start)]
        values = {mapper.init}
        for node, label, value, child in self.tree.transitions():
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
                            r!= ra.fresh,
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
                ),

                # Map to the right transition
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
                                ra.transition(mapper.map(n), l, ra.fresh) == mapper.map(c),
                            )
                        )
                    ),
                    ra.transition(mapper.map(n), l, ra.fresh) == mapper.map(c)),
            ])
            values.add(v)

        constraints.append(z3.Distinct(list(values)))
        return constraints
