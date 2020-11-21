import itertools
from typing import *

from union_find import UnionFind


# Questions:
# - Can new nodes be added to union-find in the middle of the data structure's
# lifetime? Is the inability to do so in the impl we have fundamental?
#   - Yes.  Should be able to.
# - How should we be hashing ENodes for the hashcons?

# Notes:
# Enode successors aren't pointers to e-classes; they're IDs.
# And I think we leverage that difference by using indirection on the IDs.

# Seems like Egg already has fragments of a runtime analysis (when they're
# justifying why deferred rebuilding deduplicates work).

# I think we can (need to?) argue some kind of bound on the necessary amount of
# deduplication of work in any workload.
# In practice, we may have a lot of work we can deduplicate, but we need to
# argue that in the worst case, where added and merged expressions are
# maximally different, there is some amount of duplicate work that's a function
# of the size of the term graph and the number of elements in the worklist.

# Wait. So even after we deduplicate classes in the worklist, is the amount of
# work also dependent on the level ordering in which you process e-classes?
# For example, if you have `a` and `b` as leaf nodes and they both have `+` and
# `*` as a parent (don't focus on whether this setup is possible), and you have
# [`a`, `b`, `+`, `*`] on the worklist.  Then if you merge `+` and `*`,
# do you trace through the e-class containing `+`, then the e-class containing
# `*`, if you repair `a` and `b` before processing `+` and `*`?
# Maybe not, because I think you update the union-find in the initial merge
# that added it to the worklist.
# Then what is repair doing that merge didn't?

Sym = str
EClassId = int

class Term:
    def __init__(self, sym: Sym, succs: ['Term']):
        self.sym = sym
        self.succs = succs


class ENode:
    sym: Sym
    succs: List[EClassId]
    egraph: 'EGraph'

    def __init__(self, sym: Sym, succs: List[EClassId], egraph: 'EGraph'):
        self.sym = sym
        self.succs = succs
        self.egraph = egraph

    def __hash__(self):
        res = hash(self.sym)
        succ_hashes = [hash(self.egraph.find(a)) for a in self.succs]
        for h in succ_hashes:
            res ^= h
        return res

    def __eq__(self, other):
        if not isinstance(other, ENode):
            return False
        return self.egraph.congruent(self, other)


class EClass:
    nodes: Set[ENode]
    preds: Set[ENode]

    def __init__(self, nodes: Set[ENode], preds: Set[ENode]):
        self.nodes = nodes
        self.preds = preds


# TODO use a union-find that's dynamically resizable
MAX_CLASSES = 1000

class EGraph:
    # equivalence relation over e-class IDs
    U: UnionFind
    # e-class map
    M: Dict[EClassId, EClass]
    # hashcons
    H: Dict[ENode, EClassId]

    def __init__(self):
        self.U = UnionFind(MAX_CLASSES)
        self.M = {}
        self.H = {}
        self.id_gen = 0

    ################
    # Construction #
    ################
    def add_term(self, t: Term):
        succs = [self.add_term(s) for s in t.succs]
        print(t.sym, succs)
        a = self.add(ENode(t.sym, succs, self))
        return a

    ################################
    # Low-Level Stateful Interface #
    ################################
    def add(self, n: ENode):
        if (a := self.lookup(n)) is not None:
            return a
        else:
            n = self.canonicalize(n)
            a = self.new_singleton_eclass(n)
            for succ in n.succs:
                self.M[succ].preds.add(a)
            self.H[n] = a
            return a

    def merge(self, a: EClassId, b: EClassId) -> EClassId:
        new_id = self.U.union(a, b)
        A = self.M[a]
        B = self.M[b]
        merged_class = EClass(
            A.nodes.union(B.nodes),
            A.preds.union(B.preds))
        self.M[new_id] = merged_class
        self.M[a] = merged_class
        self.M[b] = merged_class
        return new_id

    ###################
    # Utility methods #
    ###################
    def new_singleton_eclass(self, n: ENode):
        a = self.id_gen
        self.id_gen += 1
        self.M[a] = EClass({n}, set())
        return a

    def canonicalize(self, n: ENode):
        return ENode(n.sym, [self.U.find(a) for a in n.succs], self)

    def find(self, a: EClassId) -> EClassId:
        return self.U.find(a)

    def lookup(self, n: ENode) -> EClassId:
        return self.H.get(self.canonicalize(n), None)

    def congruent(self, n1: ENode, n2: ENode) -> bool:
        return n1.sym == n2.sym \
            and len(n1.succs) == len(n2.succs) \
            and all([self.find(a) == self.find(b) for a, b in zip(n1.succs, n2.succs)])

    def equiv(self, x, y) -> bool:
        if type(x) == type(y) == EClassId:
            return self.find(a) == self.find(b)
        elif isinstance(x, ENode) and isinstance(y, ENode):
            return self.lookup(x) == self.lookup(y)
        elif isinstance(x, Term) and isinstance(y, Term):
            a = self.represents(x)
            b = self.represents(y)
            return a == b
        else:
            assert False

    def represents(self, t: Term) -> ENode:
        pass


egraph = EGraph()

def t(sym, *succs):
    return Term(sym, succs)

def l(sym):
    return Term(sym, [])


plus = t('+', l('a'), l('b'))
times = t('*', l('2'), l('a'))

plus_id = egraph.add_term(plus)
times_id = egraph.add_term(times)


import pdb; pdb.set_trace()
