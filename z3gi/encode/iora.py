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
        self.param_size = dict()

    def add(self, trace):
        seq = list(itertools.chain(*map(iter, trace)))
        _ = self.tree[determinize(seq)]
        self.values.update([action.value for action in seq])
        self.input_labels.update([action.label for action in [i for (i, _) in trace]])
        self.output_labels.update([action.label for action in [o for (_, o) in trace]])
        for action in seq:
            if action.label not in self.param_size:
                self.param_size[action.label] = action.param_size()
            else:
                if self.param_size[action.label] != action.param_size():
                    raise Exception("It is not allowed to have actions with different param sizes."
                                    "Problem action: "+str(action))


    def build(self, num_locations, num_registers):
        ra = IORegisterAutomaton(list(self.input_labels), list(self.output_labels), self.param_size,
                                 num_locations, num_registers)
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
            # axiom not needed
            z3.ForAll(
                [r],
                mapper.valuation(mapper.start, r) == mapper.init
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
                        q != ra.sink,
                        r != ra.fresh
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
            # z3.ForAll(
            #     [q, l, lp, r, rp],
            #     z3.Implies(
            #         z3.And(
            #             q != ra.sink,
            #             ra.loctype(q) == False,
            #             ra.transition(q, l, r) != ra.sink,
            #             z3.Or(
            #                 r != rp,
            #                 l != lp
            #             )
            #         ),
            #         z3.Or(
            #             ra.transition(q, lp, rp) == ra.sink,
            #             rp != ra.fresh
            #         )
            #     )
            # ),
            # more readable version
            z3.ForAll(
                [q],
                z3.Implies(
                    z3.And(
                        q != ra.sink,
                        ra.loctype(q) == False,
                    ),
                    z3.And(
                        z3.Exists(
                            [r,l],
                            ra.transition(q, l, r) != ra.sink,
                        ),
                        z3.ForAll(
                            [r, l, rp,lp],
                            z3.Implies(
                                z3.And(
                                    ra.transition(q, l, r) != ra.sink,
                                    z3.Or(
                                        rp != r,
                                        lp != l,
                                    )
                                ),
                                ra.transition(q, lp, rp) == ra.sink
                            )
                        )
                    )
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
                    ra.transition(q, ra.labels[l], r) == ra.sink
                )
            )
        for l in self.input_labels])

        # Input enabled
        axioms.extend([
            z3.ForAll(
                [q, r],
                z3.Implies(
                    z3.And(
                        ra.loctype(q) == True,
                        q != ra.sink
                    ),
                    ra.transition(q, ra.labels[l], r) != ra.sink
                )
            )
        for l in self.input_labels])

        # parameter-less labels don't result in register updates
        for l in itertools.chain(self.input_labels, self.output_labels):
            if self.param_size[l] == 0:
                axioms.append(
                    z3.ForAll(
                        [q],
                        ra.update(q, ra.labels[l]) == ra.fresh
                    )
                )
        # parameter-less input labels lead to the same transition for all registers
        for l in self.input_labels:
            if self.param_size[l] == 0:
                axioms.append(
                    z3.ForAll(
                        [q,r],
                        ra.transition(q, ra.labels[l], r) == ra.transition(q, ra.labels[l], ra.fresh)
                    )
                )
        for l in self.output_labels:
            if self.param_size[l] == 0:
                axioms.append(
                    z3.ForAll(
                        [q,r],
                        z3.Implies(
                            r != ra.fresh,
                            ra.transition(q, ra.labels[l], r) == ra.sink
                        )
                    )
                )

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
            v = mapper.value(value) if value is not None else None
            c = mapper.element(child.id)
            r, rp = z3.Consts('r rp', ra.Register)

            if value is not None:
                constraints.extend([
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
                ])
            if value is not None:
                # If a non-fresh register is updated, and c and n are connected by fresh,
                # then the register contains the value
                # else the valuation is maintained.
                constraints.append(z3.ForAll(
                    [r],
                    z3.If(
                        z3.And(
                            r != ra.fresh,
                            ra.update(mapper.map(n), l) == r,
                            ra.transition(mapper.map(n), l, ra.fresh) == mapper.map(c)
                        ),
                        mapper.valuation(c, r) == v,
                        mapper.valuation(c, r) == mapper.valuation(n, r)
                    )
                ))
            else:
                constraints.append(
                    z3.ForAll(
                        [r],
                        mapper.valuation(c, r) == mapper.valuation(n, r),
                    )
                )

            # Map to the right transition
            path = [v for (_, v) in node.path() if v is not None]
            if value in path:
                if label in self.input_labels:
                    constraints.append(
                        z3.If(
                            z3.Exists(
                                [r],
                                z3.And(
                                    r != ra.fresh,
                                    mapper.valuation(n, r) == v,
                                    ra.used(mapper.map(n), r) == True
                                )
                            ),
                            z3.ForAll(
                                [r],
                                z3.Implies(
                                    z3.And(
                                        r != ra.fresh,
                                        mapper.valuation(n, r) == v,
                                        ra.used(mapper.map(n), r) == True
                                    ),
                                    ra.transition(mapper.map(n), l, r) == mapper.map(c)
                                )
                            ),
                            ra.transition(mapper.map(n), l, ra.fresh) == mapper.map(c)
                        )
                    )
                elif label in self.output_labels:
                    constraints.append(
                           z3.Exists(
                                [r],
                                z3.And(
                                    r != ra.fresh,
                                    mapper.valuation(n, r) == v,
                                    ra.used(mapper.map(n), r) == True, # this proved necessary
                                    ra.transition(mapper.map(n), l, r) == mapper.map(c)
                                )
                            )
                    )
                else:
                    raise Exception("We did something wrong")

            else:
                # the None case has been dealt in full at the axiom level
                constraints.append(
                    ra.transition(mapper.map(n), l, ra.fresh) == mapper.map(c)
                )

            if v is not None:
                values.add(v)

        constraints.append(z3.Distinct(list(values)))
        return constraints



class IORAQREncoder(Encoder):
    def __init__(self):
        self.tree = Tree(itertools.count(0))
        self.values = set()
        self.input_labels = set()
        self.output_labels = set()
        self.param_size = dict()

    def add(self, trace):
        seq = list(itertools.chain(*map(iter, trace)))
        _ = self.tree[determinize(seq)]
        self.values.update([action.value for action in seq])
        self.input_labels.update([action.label for action in [i for (i, _) in trace]])
        self.output_labels.update([action.label for action in [o for (_, o) in trace]])
        for action in seq:
            if action.label not in self.param_size:
                self.param_size[action.label] = action.param_size()
            else:
                if self.param_size[action.label] != action.param_size():
                    raise Exception("It is not allowed to have actions with different param sizes."
                                    "Problem action: "+str(action))


    def build(self, num_locations, num_registers):
        ra = IORegisterAutomaton(list(self.input_labels), list(self.output_labels), self.param_size,
                                 num_locations, num_registers)
        mapper = Mapper(ra)
        constraints = []
        constraints.extend(self.axioms(ra, mapper))
        constraints.extend(self.node_constraints(ra, mapper))
        constraints.extend(self.transition_constraints(ra, mapper))
        return ra, constraints

    def axioms(self, ra: IORegisterAutomaton, mapper: Mapper):
        #l, lp = z3.Consts('l lp', ra.Label)
        #q, qp = z3.Consts('q qp', ra.Location)
        #r, rp = z3.Consts('r rp', ra.Register)
        norm_loc = set(ra.locations).difference(set([ra.sink]))

        axioms = [
            # In the start state of the mapper,
            # all registers contain an uninitialized value.
            # axiom not needed
            z3.And([mapper.valuation(mapper.start, r) == mapper.init for r in ra.registers]),

            # The fresh register is never used
            z3.And([ra.used(q, ra.fresh) == False for q in norm_loc]),

            # If a variable is used after a transition, it means it was either used before, or it was assigned
            z3.And([
                z3.Implies(
                    z3.And(
                        ra.used(ra.transition(q, l, rp), r) == True,
                        q != ra.sink,
                        r != ra.fresh
                    ),
                    z3.Or(
                        ra.used(q, r) == True,
                        z3.And(
                            ra.update(q, l) == r,
                            rp == ra.fresh
                        ),
                    )
                ) for rp in ra.registers for r in ra.registers for l in ra.labels.values() for q in ra.locations
            ]),

            # If a variable is updated, then it should have been used.
            z3.And([
                z3.Implies(
                    z3.And(
                        r != ra.fresh,
                        ra.update(q, l) == r,
                        q != ra.sink
                    ),
                    ra.used(ra.transition(q, l, ra.fresh), r) == True
                ) for r in ra.registers for l in ra.labels.values() for q in ra.locations
                ]
            ),

            # Registers are not used in the start state
            z3.And([
                ra.used(ra.start, r) == False for r in ra.registers
            ])
        ]
        l, lp = z3.Consts('l lp', ra.Label)
        q, qp = z3.Consts('q qp', ra.Location)
        r, rp = z3.Consts('r rp', ra.Register)

        # # IO axioms
        axioms.extend([
            # The sink is labeled as an input location
            ra.loctype(ra.sink) == True,

            # Alternating input and output locations
            z3.And(
                [
                z3.If(
                    ra.loctype(q) == True,
                    z3.And([z3.Or(
                        ra.loctype(ra.transition(q, l, r)) == False,
                        ra.transition(q, l, r) == ra.sink
                    ) for l, r in itertools.product(ra.labels.values(), ra.registers)]),
                    z3.And([ra.loctype(ra.transition(q, l, r)) == True
                            for l, r in itertools.product(ra.labels.values(), ra.registers)])
                ) for q in ra.locations
                ]
            ),

            # The sink is the only rejecting state
            z3.And([
                z3.If(
                    q == ra.sink,
                    ra.output(q) == False,
                    ra.output(q) == True
                ) for q in ra.locations]
            ),

            # The start location is an input location
            ra.loctype(ra.start) == True,

            # more readable version
            z3.ForAll(
                [q],
                z3.Implies(
                    z3.And(
                        q != ra.sink,
                        ra.loctype(q) == False,
                    ),
                    z3.And(
                        z3.Exists(
                            [r, l],
                            ra.transition(q, l, r) != ra.sink,
                        ),
                        z3.ForAll(
                            [r, l, rp, lp],
                            z3.Implies(
                                z3.And(
                                    ra.transition(q, l, r) != ra.sink,
                                    z3.Or(
                                        rp != r,
                                        lp != l,
                                    )
                                ),
                                ra.transition(q, lp, rp) == ra.sink
                            )
                        )
                    )
                )
            ),

            # The sink is a sink
            z3.And([
                ra.transition(ra.sink, l, r) == ra.sink for l, r in itertools.product(ra.labels.values(), ra.registers)]
            ),

            # The sink doesn't update registers
            z3.And([
                ra.update(ra.sink, l) == ra.fresh for l in ra.labels.values()]
            )
        ])

        # From input locations, all output transitions go to sink.
        axioms.extend([
            z3.And([
                z3.Implies(
                    ra.loctype(q) == True,
                    ra.transition(q, ra.labels[l], r) == ra.sink
                )
                for q, r in itertools.product(ra.locations, ra.registers)]
            )
        for l in self.output_labels])

        # From output locations, all input transitions go to sink.
        axioms.extend([
            z3.And(
                [
                z3.Implies(
                    ra.loctype(q) == False,
                    ra.transition(q, ra.labels[l], r) == ra.sink
                ) for q,r in itertools.product(ra.locations, ra.registers)
                ]
            )
            for l in self.input_labels])

        # Input enabled
        axioms.extend([
            z3.And(
                [
                z3.Implies(
                    z3.And(
                        ra.loctype(q) == True,
                        q != ra.sink
                    ),
                    ra.transition(q, ra.labels[l], r) != ra.sink
                ) for q,r in itertools.product(ra.locations, ra.registers)]
            )
        for l in self.input_labels])

        # parameter-less labels don't result in register updates
        for l in itertools.chain(self.input_labels, self.output_labels):
            if self.param_size[l] == 0:
                axioms.append(
                    z3.And([
                        ra.update(q, ra.labels[l]) == ra.fresh for q in ra.locations]
                    )
                )
        # parameter-less input labels lead to the same transition for all registers
        for l in self.input_labels:
            if self.param_size[l] == 0:
                axioms.append(
                    z3.And(
                        [
                        ra.transition(q, ra.labels[l], r) == ra.transition(q, ra.labels[l], ra.fresh)
                        for q,r in itertools.product(ra.locations, ra.registers)]
                    )
                )
        for l in self.output_labels:
            if self.param_size[l] == 0:
                axioms.append(
                    z3.And(
                        [
                        z3.Implies(
                            r != ra.fresh,
                            ra.transition(q, ra.labels[l], r) == ra.sink
                        ) for q,r in itertools.product(ra.locations, ra.registers)]
                    )
                )

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
            v = mapper.value(value) if value is not None else None
            c = mapper.element(child.id)
           # r, rp = z3.Consts('r rp', ra.Register)

            if value is not None:
                constraints.extend([
                    # If a non-fresh register has changed, it must have been updated
                    z3.And(
                        [
                        z3.Implies(
                            z3.And(
                                r != ra.fresh,
                                mapper.valuation(c, r) != mapper.valuation(n, r)
                            ),
                            ra.update(mapper.map(n), l) == r
                        ) for r in ra.registers]
                    ),

                    # If a used, non-fresh register keeps its value, then it was not updated.
                    z3.And(
                        [
                        z3.Implies(
                            z3.And(
                                r != ra.fresh,
                                mapper.valuation(c, r) == mapper.valuation(n, r),
                                ra.used(mapper.map(n), r) == True
                            ),
                            ra.update(mapper.map(n), l) != r
                        ) for r in ra.registers]
                    ),
                ])
            if value is not None:
                # If a non-fresh register is updated, and c and n are connected by fresh,
                # then the register contains the value
                # else the valuation is maintained.
                constraints.append(z3.And(
                    [
                    z3.If(
                        z3.And(
                            r != ra.fresh,
                            ra.update(mapper.map(n), l) == r,
                            ra.transition(mapper.map(n), l, ra.fresh) == mapper.map(c)
                        ),
                        mapper.valuation(c, r) == v,
                        mapper.valuation(c, r) == mapper.valuation(n, r)
                    ) for r in ra.registers]
                ))
            else:
                constraints.append(
                    z3.And(
                        [
                        mapper.valuation(c, r) == mapper.valuation(n, r)
                        for r in ra.registers]
                    )
                )

            # Map to the right transition
            path = [v for (_, v) in node.path() if v is not None]
            if value in path:
                if label in self.input_labels:
                    constraints.append(
                        z3.If(
                            z3.Or(
                                [
                                z3.And(
                                    r != ra.fresh,
                                    mapper.valuation(n, r) == v,
                                    ra.used(mapper.map(n), r) == True
                                ) for r in ra.registers]
                            ),
                            z3.And(
                                [
                                z3.Implies(
                                    z3.And(
                                        r != ra.fresh,
                                        mapper.valuation(n, r) == v,
                                        ra.used(mapper.map(n), r) == True
                                    ),
                                    ra.transition(mapper.map(n), l, r) == mapper.map(c)
                                )
                                for r in ra.registers]
                            ),
                            ra.transition(mapper.map(n), l, ra.fresh) == mapper.map(c)
                        )
                    )
                elif label in self.output_labels:
                    constraints.append(
                           z3.Or(
                                [
                                z3.And(
                                    r != ra.fresh,
                                    mapper.valuation(n, r) == v,
                                    ra.used(mapper.map(n), r) == True, # this proved necessary
                                    ra.transition(mapper.map(n), l, r) == mapper.map(c)
                                )
                               for r in ra.registers]
                            )
                    )
                else:
                    raise Exception("We did something wrong")

            else:
                # the None case has been dealt in full at the axiom level
                constraints.append(
                    ra.transition(mapper.map(n), l, ra.fresh) == mapper.map(c)
                )

            if v is not None:
                values.add(v)

        constraints.append(z3.Distinct(list(values)))
        return constraints
