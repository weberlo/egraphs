import itertools
import time
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

# TODO count both find and repair calls and modify the worklist processing
# scheme (see if randomly reordering the worklist changes the number of repair
# calls. if so, we have good evidence both that rebuilding obtains an
# asymptotic improvement *and* that there is further work that can be done on
# clever ordering of worklist processing).
# After randomizing, trying different level orderings could be fruitful (i.e.,
# process the e-classes from highest to lowest in the tree *or* do the reverse).

# TODO add asserts for different invariants (e.g., congruence and hashcons) in
# in the e-graph where the invariant must hold
# TODO figure out where each invariant must hold

# TODO as long as we always access self.M with self.M[self.find(a)], instead of
# self.M[a], we can get rid of the non-canonical mapping when we merge.

# If you have a completely linear expr tree (e.g., f(f(f(...(a))))), is it the
# case that lazy rebuilding saves you nothing? Or is this precisely the perfect
# case when you might want to reorder how the worklist is being processed?

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

    def __init__(self, sym: Sym, succs: List[EClassId]):
        self.sym = sym
        self.succs = succs

    def __hash__(self):
        # TODO we never modify the function symbol or the successors, so we can
        # precompute the hash, especially since we (I think) always
        # canonicalize nodes (creating a new one) before using them.
        # This will be important when we start counting finds!
        # Well... maybe not. Depends on whether we hash the canonicalized
        # e-node more than once. If we do, then we should precompute, if we
        # don't, then it doesn't matter, since we only compute it once either
        # way.

        # generic XOR hash on recursive datatypes
        res = hash(self.sym)
        succ_hashes = [hash(a) for a in self.succs]
        for h in succ_hashes:
            res ^= h
        return res

    def __eq__(self, other):
        if not isinstance(other, ENode):
            return False
        # NOTE this is *not* congruence, because we're not searching for the
        # canonical e-class IDs. The main place this function is used is for
        # the hashcons, where ENodes are keys, and it's the job of the e-graph
        # to canonicalize the entries, not the ENode equality function.
        #
        # Using `egraph.congruent` also incurs a shit-ton of `find` calls.
        return self.sym == other.sym and \
            len(self.succs) == len(other.succs) and \
            all(a == b for (a, b) in zip(self.succs, other.succs))

    def __repr__(self) -> str:
        return f'({self.sym}) -> {self.succs}'


class EClass:
    nodes: Set[ENode]
    preds: Dict[ENode, EClassId]

    def __init__(self, nodes: Set[ENode], preds: Dict[ENode, EClassId]):
        self.nodes = nodes
        self.preds = preds


class EGraph:
    # equivalence relation over e-class IDs
    U: UnionFind
    # e-class map
    M: Dict[EClassId, EClass]
    # hashcons
    H: Dict[ENode, EClassId]

    def __init__(self, **opts):
        self.U = UnionFind()
        self.M = {}
        self.H = {}
        self.worklist = []
        self.num_repairs = 0

        self.debug = opts.get('debug', True)
        self.lookup_compression = opts.get('lookup_compression', False)
        self.strict_rebuilding = opts.get('strict_rebuilding', True)

    ################
    # Construction #
    ################
    def add_term(self, t: Term):
        # add term bottom-up
        succs = [self.add_term(s) for s in t.succs]
        # print(t.sym, succs)
        a = self.add(ENode(t.sym, succs))
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
                self.M[succ].preds[n] = a
            self.H[n] = a
            return a

    def merge(self, a: EClassId, b: EClassId) -> EClassId:
        if (canon := self.find(a)) == self.find(b):
            return canon
        # update (e-class ID -> e-class) map so `a` and `b` now point to the
        # same merged e-class
        A = self.M[a]
        B = self.M[b]
        # TODO how do we handle merging the two `preds` dictionaries?
        # do we need to do canonicalization? we probably want to push that
        # until rebuilding (even though we're currently doing strict
        # rebuilding, we want to design this so it allows both eventually).
        # Yeah. we don't need to do that here. we should even assert that all
        # of the keys are distinct.
        # No. They're not necessarily distinct, because they may be nodes that
        # are both args of the same parent function.
        # Really, we want to ensure they both point to the same e-class
        if self.debug:
            for k in (A.preds.keys() & B.preds.keys()):
                assert A.preds[k] == B.preds[k]

        new_preds = A.preds.copy()
        new_preds.update(B.preds)
        merged_class = EClass(
            A.nodes.union(B.nodes),
            new_preds)

        new_id = self.U.union(a, b)
        self.worklist.append(new_id)
        self.M[new_id] = merged_class
        self.M[a] = merged_class
        self.M[b] = merged_class

        if self.strict_rebuilding:
            self.rebuild()

        return new_id

    def rebuild(self):
        while len(self.worklist) != 0:
            deduped = {self.find(eclass) for eclass in self.worklist}
            self.worklist.clear()
            for eclass in deduped:
                self.repair(eclass)

    def repair(self, a):
        self.num_repairs += 1
        A = self.M[a]
        # ensure canonical ENodes point to canonical EClasses in the hashcons
        # by recanonicalizing nodes in `A`s dictionary of parents and finding
        # the new canonical e-class they should point to.
        for (p_enode, p_eclass) in A.preds.items():
            if p_enode in self.H:
                del self.H[p_enode]
            p_node = self.canonicalize(p_enode)
            self.H[p_enode] = self.find(p_eclass)

        # since we've changed the equivalence relation, we also may now have
        # parent e-nodes of this e-class who are congruent (previously, they
        # would have had the same e-node symbol but their children
        # would have had different canonical e-classes), meaning we need to
        # merge them to compute the closure (in the rebuilding paradigm, we
        # again just add them to the worklist).
        new_parents = {}
        for (p_enode, p_eclass) in A.preds.items():
            p_enode = self.canonicalize(p_enode)
            if p_enode in new_parents:
                # this node is congruent to another (previously distinct) node
                # in `A`s parents, since its canonical representation is now
                # equivalent to that node's.
                canon_p_eclass = self.merge(p_eclass, new_parents[p_enode])
            else:
                canon_p_eclass = self.find(p_eclass)
            new_parents[p_enode] = canon_p_eclass
        A.preds = new_parents

    ###################
    # Utility methods #
    ###################
    def new_singleton_eclass(self, n: ENode):
        a = self.U.add_set()
        self.M[a] = EClass({n}, {})
        return a

    def canonicalize(self, n: ENode):
        return ENode(n.sym, [self.U.find(a) for a in n.succs])

    def find(self, a: EClassId) -> EClassId:
        return self.U.find(a)

    def lookup(self, n: ENode) -> Optional[EClassId]:
        # TODO I haven't seen this optimization mentioned anywhere.  Is this new?!  Is this sound?!
        # The idea is that you update the hashcons on the fly, in the same way
        # that you do path compression in union-find.
        #
        # Note that for testing, `lookup` is only used for `equiv` checks and
        # for `add`, so it shouldn't affect `merge` results.
        #
        # Looks like egg does something similar:
        #   https://github.com/egraphs-good/egg/blob/39415f19acdacd6dde62f40cb2bb08f8669acc85/src/egraph.rs#L266
        # Weird. They have their own union-find impl where classes are unioned by whichever one has the lower ID???
        #   https://github.com/egraphs-good/egg/blob/39415f19acdacd6dde62f40cb2bb08f8669acc85/src/unionfind.rs#L53
        # I'd like to say this is just arbitrary, but the note in the link above says egg relies on this behavior!
        #
        # Nevermind about them doing something similar.  Essentially, all they're doing in their lookup impl is
        #   a = self.H.get(self.canonicalize(n), None)
        #   if a is not None:
        #     a = self.find(a)
        #   return a
        # Comparing this to the original code presented in the paper, it's just layering an extra `find` at the end:
        #   return self.H.get(self.canonicalize(n), None)
        # It looked different, because they have one difference, which is they
        # will mutably update the given enode `n` to be canonicalized upon
        # return (kinda gross but maybe it has a use case), but they are not updating the hashcons.

        if self.lookup_compression:
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
        else:
            a = self.H.get(self.canonicalize(n), None)
            if a is not None:
                a = self.find(a)
            return a

    def congruent(self, n1: ENode, n2: ENode) -> bool:
        return n1.sym == n2.sym \
            and len(n1.succs) == len(n2.succs) \
            and all([self.find(a) == self.find(b) for a, b in zip(n1.succs, n2.succs)])

    def equiv(self, x, y) -> bool:
        if type(x) == type(y) == EClassId:
            return self.find(x) == self.find(y)
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
        return self.lookup(ENode(t.sym, succ_ids))

    ################
    # Benchmarking #
    ################
    def report(self):
        return {
            'num_repairs': self.num_repairs,
            'num_finds': self.U.num_finds
            # NOTE no sense in printing these out, as they're always equal to
            # the number of vertices
            # 'hashcons_size': len(self.H),
            # 'eclass_map_size': len(self.M)
        }

    def reset_op_counts(self):
        self.num_repairs = 0
        self.U.num_finds = 0


def t(sym, *succs):
    return Term(sym, succs)


def test_basic():
    egraph = EGraph()

    a_plus_a = t('+', t('a'), t('a'))
    a_plus_b = t('+', t('a'), t('b'))
    two_times_a = t('*', t('2'), t('a'))
    # a_lshift_one = t('<<', t('a'), t('1'))

    a_plus_a_id = egraph.add_term(a_plus_a)
    a_plus_b_id = egraph.add_term(a_plus_b)
    two_times_a_id = egraph.add_term(two_times_a)

    egraph.merge(a_plus_a_id, two_times_a_id)

    assert not egraph.equiv(a_plus_a, a_plus_b)
    assert egraph.equiv(a_plus_a, two_times_a)

    a_id = egraph.represents(t('a'))
    b_id = egraph.represents(t('b'))
    assert a_id != b_id
    egraph.merge(a_id, b_id)
    a_id = egraph.represents(t('a'))
    b_id = egraph.represents(t('b'))
    assert a_id == b_id
    assert egraph.equiv(a_plus_a, a_plus_b)
    print('done!')


def test_nelson_oppen_fig1():
    egraph = EGraph()
    a = t('a')
    b = t('b')
    f = t('f', a, b)
    f_f = t('f', f, b)

    f_f_id = egraph.add_term(f_f)
    f_id = egraph.add_term(f)
    a_id = egraph.add_term(a)
    b_id = egraph.add_term(b)

    assert not egraph.equiv(f_f_id, a_id)  # f(f(a, b), b) != a
    assert not egraph.equiv(f_f_id, f_id)  # f(f(a, b), b) != f(a, b)

    egraph.merge(f_id, a_id)  # assert f(a, b) = a

    assert egraph.equiv(f_id, a_id)        # f(a, b) = a
    assert egraph.equiv(f_f_id, a_id)      # f(f(a, b), b) = a
    assert egraph.equiv(f_f_id, f_id)      # f(f(a, b), b) = f(a, b)
    assert not egraph.equiv(f_f_id, b_id)  # f(f(a, b), b) != b
    assert not egraph.equiv(f_id, b_id)    # f(a, b) != b
    assert not egraph.equiv(a_id, b_id)    # a != b
    print('done!')


def setup_linear_graph(egraph, n):
    """
    Create graph of f(f(...(a))), where `f` is applied `n` times, giving
    `n+1` vertices overall.
    """
    curr = t('a')
    terms = [curr]
    for _ in range(n):
        curr = t('f', curr)
        terms.append(curr)

    term_ids = []
    for term in terms:
        term_ids.append(egraph.add_term(term))

    for i, term_id in enumerate(term_ids):
        for term2_id in term_ids[:i]:
            assert not egraph.equiv(term_id, term2_id)
    egraph.reset_op_counts()
    return term_ids


def test_nelson_oppen_fig2_strict():
    egraph = EGraph(strict_rebuilding=True)
    term_ids = setup_linear_graph(egraph, 5)

    # f(f(f(f(f(a))))) = a
    egraph.merge(term_ids[0], term_ids[-1])
    print(egraph.report())
    egraph.reset_op_counts()
    assert egraph.equiv(term_ids[0], term_ids[-1])
    # ensure we've generated no new node equivalences other than the ones we
    # merged.
    for i, term_id in enumerate(term_ids):
        for term2_id in term_ids[1:i]:
            assert not egraph.equiv(term_id, term2_id)

    # f(f(f(a))) = a
    egraph.merge(term_ids[0], term_ids[3])
    print(egraph.report())
    egraph.reset_op_counts()
    # everything should now be equivalent
    for (t1_id, t2_id) in itertools.combinations(term_ids, 2):
        assert egraph.equiv(t1_id, t2_id)
    print('done!')


def test_nelson_oppen_fig2_lazy():
    egraph = EGraph(strict_rebuilding=False)
    term_ids = setup_linear_graph(egraph, 5)

    # f(f(f(f(f(a))))) = a
    egraph.merge(term_ids[0], term_ids[-1])
    # f(f(f(a))) = a
    egraph.merge(term_ids[0], term_ids[3])
    # ensure we haven't prematurely processed anything
    assert len(egraph.worklist) == 2
    egraph.rebuild()
    print(egraph.report())
    egraph.reset_op_counts()
    # everything should now be equivalent
    for (t1_id, t2_id) in itertools.combinations(term_ids, 2):
        assert egraph.equiv(t1_id, t2_id)
    print('done!')


def find_worst_input_for_linear():
    # Results for N=100:
    #   Lazy:
    #     max_repairs_item={'num_repairs': 99, 'num_finds': 1930, 'idx': 1}
    #     max_finds_item={'num_repairs': 99, 'num_finds': 1930, 'idx': 1}
    #
    #   Strict:
    #     max_repairs_item={'num_repairs': 100, 'num_finds': 13694, 'idx': 1}
    #     max_finds_item={'num_repairs': 100, 'num_finds': 13694, 'idx': 1}
    #
    # Conclusion: merging `a` with the top of the `f` chain, then `f(a)` with
    # the top of the `f` chain gives the worst number of finds.
    #
    # NOTE We can't try out the ordering heuristic on this linear graph, because the worklist
    # is always length 1 (except at the beginning where we add two merge calls,
    # but even then, both of them get deduped to the same e-class).
    def run_with_strictness(strict):
        N = 100
        results = []
        for i in range(1, N+1):
            print(f'testing {i}')
            egraph = EGraph(strict_rebuilding=strict)
            term_ids = setup_linear_graph(egraph, N)
            # First, try optimizing with the first `merge` call held constant.
            egraph.merge(term_ids[0], term_ids[-1])
            egraph.merge(term_ids[i], term_ids[-1])
            start_time = time.time()
            egraph.rebuild()
            rebuild_time = time.time() - start_time
            report = egraph.report()
            results.append(dict(report, idx=i, rebuild_time=rebuild_time))
        max_repairs_item = max(results, key=lambda d: d['num_repairs'])
        max_finds_item = max(results, key=lambda d: d['num_finds'])
        max_rebuild_time_item = max(results, key=lambda d: d['rebuild_time'])
        print(f'{max_repairs_item=}')
        print(f'{max_finds_item=}')
        print(f'{max_rebuild_time_item=}')

    run_with_strictness(False)
    run_with_strictness(True)


def plot_asymptotics_on_linear():
    # TODO fix index of second merge to be 1 and vary `N`
    def run_with_strictness(strict):
        results = []
        for N in range(1, 101):
            egraph = EGraph(strict_rebuilding=strict)
            term_ids = setup_linear_graph(egraph, N)
            egraph.merge(term_ids[0], term_ids[-1])
            egraph.merge(term_ids[1], term_ids[-1])
            start_time = time.time()
            egraph.rebuild()
            rebuild_time = time.time() - start_time
            report = egraph.report()
            results.append(dict(report, idx=i, rebuild_time=rebuild_time))
        return results

    res = run_with_strictness(False)
    import pdb; pdb.set_trace()
    # run_with_strictness(True)

# TODO after plotting asymptotics, there are three "extreme" inputs to consider:
# - the one outlined in the egg paper
# - a generalization of nelson-oppen figure 1 (the f(f(a, b), b) = b example)
# - some kind of complete tree

def main():
    # test_basic()
    # test_nelson_oppen_fig1()
    # test_nelson_oppen_fig2_strict()
    # test_nelson_oppen_fig2_lazy()
    # test_linear_lazy()
    find_worst_input_for_linear()


if __name__ == '__main__':
    main()
