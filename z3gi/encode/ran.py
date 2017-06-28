import itertools
import z3

from encode import Encoder
from define.ra import SimpleRegisterAutomaton


class RANEncoder(Encoder):
    def __init__(self):
        self.trie = RANEncoder.Trie(itertools.count(0))
        self.cache = {}
        self.values = set()

    def add(self, trace):
        seq, accept = trace
        node = self.trie[determinize(seq)]
        self.cache[node] = accept
        self.values.update([action.value for action in seq])

    def build(self, ra, initialized=True):
        mapper = RANEncoder.Mapper(ra)
        return self.axioms(ra, mapper, initialized) + \
               self.output_constraints(ra, mapper) + \
               self.transition_constraints(ra, mapper)

    def print_tree(self):
        print(self.trie)

    @staticmethod
    def axioms(ra : SimpleRegisterAutomaton, mapper, initialized):
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
                    z3.And(
                        ra.used(ra.transition(q, l, rp), r) == True
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
        r = z3.Const('r', ra.Register)
        rp = z3.Const('rp', ra.Register)
        for node, accept in self.cache.items():
            n = mapper.element(node.id)
            constraints.extend(
                [ra.output(mapper.map(n)) == accept,
                 # z3.ForAll([r,rp],
                 #           z3.Implies(
                 #               z3.And(
                 #               r != rp,
                 #               r != ra.fresh,
                 #               rp != ra.fresh
                 #               ),
                 #               mapper.valuation(n, r) != mapper.valuation(n, rp)
                 #           )
                 #        )
                ]
            )

        return constraints

    def transition_constraints(self, ra, mapper):
        constraints = [ra.start == mapper.map(mapper.start)]
        values = {mapper.init}
        for node, label, value, child in self.trie.transitions():
            n = mapper.element(node.id)
            l = ra.labels[label]
            v = mapper.value(value)
            c = mapper.element(child.id)
            r = z3.Const('r', ra.Register)
            rp = z3.Const('rp', ra.Register)

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
                # and the transition
                # what if not used?
                z3.ForAll(
                    [r],
                    z3.Implies(
                        z3.And(
                            r != ra.fresh,
                            mapper.valuation(c, r) != mapper.valuation(n, r)),
                        ra.update(mapper.map(n), l) == r
                    )
                ),

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

                # If a register is updated, then the node reached with a fresh transition must contain the new value
                # or
                # z3.ForAll(
                #     [r],
                #     z3.If(
                #         z3.And(
                #             r != ra.fresh,
                #             ra.update(mapper.map(n), l) == r,
                #             ra.transition(mapper.map(n), l, ra.fresh) == mapper.map(c)
                #         ),
                #         mapper.valuation(c, r) == v,
                #         mapper.valuation(c, r) == mapper(n, r)
                #     )
                # ),

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

    @staticmethod
    class Trie(object):
        def __init__(self, counter):
            self.id = next(counter)
            self.counter = counter
            self.children = {}

        def __getitem__(self, seq):
            trie = self
            for label, value in seq:
                if (label, value) not in trie.children:
                    trie.children[(label, value)] = RANEncoder.Trie(self.counter)
                trie = trie.children[(label, value)]
            return trie

        def __iter__(self):
            yield self
            for node in itertools.chain(*map(iter, self.children.values())):
                yield node

        def transitions(self):
            for node in self:
                for label, value in node.children:
                    yield node, label, value, node.children[(label, value)]

        def __str__(self, tabs=0):
            space = "".join(["\t" for _ in range(0,tabs)])
           # print(space, "n", self.id)
            tree = "(n{0}".format(self.id)
            for label, value in self.children:
                tree+= "\n" + space + " {0} -> {1}".format(value, self.children[(label, value)].__str__(tabs=tabs+1))
            tree += ")"
            return tree


    @staticmethod
    class Mapper(object):
        def __init__(self, ra):
            self.Value = z3.DeclareSort('Value')
            self.Element = z3.DeclareSort('Element')
            self.start = self.element(0)
            self.init = self.value("_")
            self.map = z3.Function('map', self.Element, ra.Location)
            self.valuation = z3.Function('valuation', self.Element, ra.Register, self.Value)

        def value(self, name):
            return z3.Const("v"+str(name), self.Value)

        def element(self, name):
            return z3.Const("n"+str(name), self.Element)


def determinize(seq):
    neat = {}
    i = 0
    for (label, value) in seq:
        if value not in neat:
            neat[value] = i
            i = i + 1
    return [(label, neat[value]) for label, value in seq]
