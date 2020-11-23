import itertools
from typing import *

from union_find import UnionFind


# Questions:
# - Can new nodes be added to union-find in the middle of the data structure's
# lifetime? Is the inability to do so in the impl we have fundamental?
#   - Yes.  Should be able to.
# - How should we be hashing ENodes for the hashcons?
#   - Recursively XOR symbols
# - What is a canonical e-node (as opposed to a canonical e-class)?
#   - There is a canonical representation of an e-node, which if the node's
#   symbol is `f`, is `f(find(a_1), find(a_2), ...)`.

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

# When we add an enode `n`, the reason we store both the eclass ID *and* the
# enode in `n`s children's predecessors is so we can later update the hashcons
# for `n` when the *childrens*' eclasses are merged. This is because the
# hashcons needs to map from *canonicalized* nodes to canonical e-classes, and
# an e-node's canonicalized representation may change if one of its children is
# merged with another e-class (i.e., if the canonical e-class for one of its
# children changes).

# No wonder the definition of congruence seems so strange. It's defined such
# that two nodes are congruent if their function symbols are identical and all
# of their children are equivalent.
# The definition is almost begging for the closure to be taken!
# The naive way you might do this is by considering every pair of nodes with
# equivalent function symbols, then checking if each of their children are in
# the same equivalence partition. If so, add the two nodes to the equivalence
# relation, and repeat.
#
# Really all the congruence invariant is stating then is that after you merge
# two equivalence partitions, if there are any new congruent pairs of nodes,
# the equivalence relation needs to be grown to include them.
# That is, every time you merge two classes, you need to "propagate" the change
# to the equivalence relation by computing the new congruence closure.
#
# The core innovation of egg is that you don't need to maintain this congruence
# invariant *immediately* after merging.
#
# If we add another level of indirection to the hashcons, can we get away with
# restoring the hashcons invariant less frequently? Currently, we need to
# update the mapping if *either* the node's canonical representation changes
# (one of its childrens canonical e-class changes) or if the e-class it maps to
# is no longer the canonical e-class (it was merged with another e-class).
# So instead, maybe we have a map from a node's canonical repr to a node id (the node id
# never chnages) *and* a map from node id to canonical e-class.
# (Note you may have unused, outdated mappings in the former map, since the canonical
# repr may change, meaning you'll no longer key into outdated canonical reprs)
# When a node's canonical repr changes, update the former map.
# When a node's canonical e-class changes, update the latter map.
# Does that improve things?
#
# TODO Space increase concerns. If you have unused mappings in the (node ->
# node id) map, will the number of them grow to be exponential if not removed?
# Is there a slick way we can remove them? Well, we know when they change. It's
# when you merge any of their children. What have you gained then? You still
# need to update the hashcons on a merge. Well, when does the canonical e-class
# change? When the node's canonical e-class (not its children) changes.
#
#
# Back to the idea of ordering your merges. It does matter! Rebuild runs until
# fix point (when there are no merge requests generated by the previous iter).
# They note that it's good they chunk the requests, because in later
# iterations, the equivalence relation has changed, so now they can deduplicate more e-classes.
# So we can either improve things by ordering somehow according to the
# structure of the tree or maybe using a different kind of data structure for
# the worklist!
# Look more at the second stanza of the repair pseudocode.
# Also, once we implement repair, we can measure algorithm performance by the
# number of repair calls, because the egg paper shows the correlation with
# runtime is very strong.

# Union find is using the wrong "rank" when it does union by rank, because
# whereas the ranks are defined by the number of nodes in the e-class, when
# merging two e-classes, we care about reducing the number of parent nodes for
# which we need to restore the hashcons invariant. So we want to ensure that
# whichever e-class has more parent nodes will become the canonical e-class,
# because then we only need to update the hashcons of the e-class with fewer
# parent nodes.
# To do so, we need access to the union-find data structure to enforce which
# node becomes canonical.
# TODO this might break the union-by-rank bound improvements in union find
# TODO does this modification give us asymptotic improvements at the e-graph level?
# TODO do the two concerns above balance out or does one dominate?
# DST *does* modify union-find to assert that union(e1, e2) makes e1 the
# canonical. Do they maintain the bounds?
# TODO Can we relate the number of parents an e-class has with its rank in the
# underlying union-find?

# TODO We can model congruence closure as an online algorithm, where we have
# merge calls and query calls (the congruence invariant must hold after every query).
# With nelson-oppen, they're treating it as if you have a query call after every merge call.
# Egg develops an algorithm that works under the assumption that you have many
# merges before you have a query.
# In both cases, you have a set of merges to process to maintain congruence.
# After every merge call you process, you may generate more merge calls
# (because of upward merging required to restore the hashcons invariant in
# parents) to process. In the Nelson-Oppen case, they process all new generated
# merges before the query is processed.
# When you delay processing merges, each merge you process can obviate the need
# for subsequent merges, but it can also generate new merges.
# So there's a natural question about how to order merges to maximize
# deduplication and minimize the number of generated merges.

# You may also allow the algorithm to "peek into" the query to see which
# subtree its looking at and only process the merges relevant to that subtree.

# This means what we said about rebuilding being related to the new equality
# saturation use case is actually wrong. It gives improvements even within the
# original congruence closure use case!

# After we analyze just with merges and queries, we can think about how `add`
# calls fit in (i.e., the equality saturation use case).

# TODO count both find and repair calls and modify the worklist processing scheme ().

Sym = str
EClassId = int

class Term:
    def __init__(self, sym: Sym, succs: ['Term']):
        self.sym = sym
        self.succs = succs

    def is_leaf(self):
        return len(self.succs) == 0


class ENode:
    sym: Sym
    succs: List[EClassId]
    egraph: 'EGraph'

    def __init__(self, sym: Sym, succs: List[EClassId], egraph: 'EGraph'):
        self.sym = sym
        self.succs = succs
        self.egraph = egraph

    def __hash__(self):
        # generic XOR hash on recursive datatypes
        res = hash(self.sym)
        succ_hashes = [hash(self.egraph.find(a)) for a in self.succs]
        for h in succ_hashes:
            res ^= h
        return res

    def __eq__(self, other):
        if not isinstance(other, ENode):
            return False
        return self.egraph.congruent(self, other)

    def __repr__(self) -> str:
        return f'({self.sym}) -> {self.succs}'



class EClass:
    nodes: Set[ENode]
    preds: Set[Tuple[ENode, EClassId]]

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
                self.M[succ].preds.add((n, a))
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
        # ensure canonical ENodes point to canonical EClasses in the hashcons
        for (p_node, p_eclass) in merged_class.preds:
            del self.H[p_node]
            p_node = self.canonicalize(p_node)
            self.H[p_node] = self.find(p_eclass)
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

    def lookup(self, n: ENode) -> Optional[EClassId]:
        # TODO I haven't seen this optimization mentioned anywhere.  Is this new?!  Is this sound?!
        # The idea is that you update the hashcons on the fly, in the same way
        # that you do path compression in union-find.

        # Original code
        # return self.H.get(self.canonicalize(n), None)

        canon_n = self.canonicalize(n)
        a = self.H.get(canon_n, None)
        if a is None:
            return None
        elif (canon_a := self.find(a)) != a:
            # `n`s canonical repr isn't mapped to a canonical e-class
            # del self.H[canon_n]
            self.H[canon_n] = canon_a
            return canon_a
        else:
            return a

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
            return a is not None and b is not None and (a == b)
        else:
            assert False

    def represents(self, t: Term) -> Optional[EClassId]:
        succ_ids = [self.represents(s) for s in t.succs]
        if any(map(lambda a: a == None, succ_ids)):
            return None
        return self.lookup(ENode(t.sym, succ_ids, self))


egraph = EGraph()

def t(sym, *succs):
    return Term(sym, succs)

def l(sym):
    return Term(sym, [])


a_plus_a = t('+', l('a'), l('a'))
a_plus_b = t('+', l('a'), l('b'))
two_times_a = t('*', l('2'), l('a'))

a_plus_a_id = egraph.add_term(a_plus_a)
a_plus_b_id = egraph.add_term(a_plus_b)
two_times_a_id = egraph.add_term(two_times_a)

egraph.merge(a_plus_a_id, two_times_a_id)

assert not egraph.equiv(a_plus_a, a_plus_b)
assert egraph.equiv(a_plus_a, two_times_a)

import pdb; pdb.set_trace()
