import itertools


class Tree(object):
    def __init__(self, counter):
        self.id = next(counter)
        self.counter = counter
        self.children = {}

    def __getitem__(self, seq):
        trie = self
        for action in seq:
            if action not in trie.children:
                trie.children[action] = Tree(self.counter)
            trie = trie.children[action]
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
        space = "".join(["\t" for _ in range(0, tabs)])
        tree = "(n{0}".format(self.id)
        for label, value in self.children:
            tree += "\n" + space + " {0} -> {1}".format(value, self.children[(label, value)].__str__(tabs=tabs + 1))
        tree += ")"
        return tree


def determinize(seq):
    neat = {}
    i = 0
    for (label, value) in seq:
        if value not in neat:
            neat[value] = i
            i = i + 1
    return [(label, neat[value]) for label, value in seq]