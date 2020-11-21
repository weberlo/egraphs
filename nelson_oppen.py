import itertools

from union_find import UF

ID_GEN = 0

class ENode:
    def __init__(self, label):
        global ID_GEN
        self.label = label
        self.id = ID_GEN
        ID_GEN += 1
        # NOTE order of successors matters
        self.succs = []
        # NOTE order of predecessors matters
        self.preds = []


# # Seems different from a standard union-find, because you don't need a
# # representative node. The e-class itself works as a representative, and you can
# # use pointer equality to check if two e-classes are equal.

# # Well no, because you need to be able to do merges on nodes---not classes. So
# # each node needs a pointer to its eclass

# class EClass:
#     def __init__(self, node):
#         self.nodes = [node]


class EGraph:
    def __init__(self, eqs):
        # TODO use eqs
        # NOTE we're following nelson-oppen figure 1
        self.v1 = ENode('f')
        self.v2 = ENode('f')
        self.v3 = ENode('a')
        self.v4 = ENode('b')
        self.nodes = [self.v1, self.v2, self.v3, self.v4]

        self.R = UF(len(self.nodes))

        self.v1.preds = []
        self.v1.succs = [self.v2, self.v4]

        self.v2.preds = [self.v1]
        self.v2.succs = [self.v3, self.v4]

        self.v3.preds = [self.v2]
        self.v3.succs = []

        self.v4.preds = [self.v2, self.v1]
        self.v4.succs = []

    def preds(self, n):
        # FIXME inefficient
        cls_id = self.R.find(n.id)
        res = []
        for i, nn in enumerate(self.nodes):
            if self.R.find(i) == cls_id:
                res += nn.preds
        return res

    def merge(self, n1, n2):
        if self.R.find(n1.id) == self.R.find(n2.id):
            return
        n1_preds = self.preds(n1)
        n2_preds = self.preds(n2)
        self.R.union(n1.id, n2.id)

        for (x, y) in itertools.product(n1_preds, n2_preds):
            if (self.R.find(x.id) != self.R.find(y.id)) and (self.congruent(x, y)):
                self.merge(x, y)

    def congruent(self, n1, n2):
        if len(n1.succs) != len(n2.succs):
            return False
        for i in range(len(n1.succs)):
            if self.R.find(n1.succs[i].id) != self.R.find(n2.succs[i].id):
                return False
        return True


g = EGraph([])
[v1, v2, v3, v4] = g.nodes
g.merge(v2, v3)
import pdb; pdb.set_trace()

# fig1 = ...
