import itertools
import matplotlib
import matplotlib.pyplot as plt
import time
from typing import *
from math import log2

from union_find import UnionFind

Sym = str
EClassId = int

class Term:
    def __init__(self, sym: Sym, succs: ['Term']):
        self.sym = sym
        self.succs = succs

    def is_leaf(self):
        return len(self.succs) == 0

    def __repr__(self):
        if len(self.succs) == 0:
            return f'{self.sym}'
        else:
            succ_reprs = ' '.join(map(repr, self.succs))
            return f'({self.sym} {succ_reprs})'


class ENode:
    sym: Sym
    succs: List[EClassId]

    def __init__(self, sym: Sym, succs: List[EClassId]):
        self.sym = sym
        self.succs = succs

    def __hash__(self):
        # generic XOR hash over all fields in data-type
        res = hash(self.sym)
        succ_hashes = [hash(a) for a in self.succs]
        for h in succ_hashes:
            res ^= h
        return res

    def __eq__(self, other):
        if not isinstance(other, ENode):
            return False
        return self.sym == other.sym and \
            len(self.succs) == len(other.succs) and \
            all(a == b for (a, b) in zip(self.succs, other.succs))

    def __repr__(self) -> str:
        return f'({self.sym} {self.succs})'


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
        self.U = UnionFind(deterministic=True)
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

        # naive merging
        new_id = self.U.union(a, b)
        
        # # modify by smaller half. cf. DST
        # if len(A.preds) <= len(B.preds):
        #   # old_a = self.U.find(a)
        #   new_id = self.U.union(b, a)
        #   # assert(old_a == self.U.find(new_id))
        # else:
        #   # old_b = self.U.find(b)
        #   new_id = self.U.union(a, b)
        #   # assert(old_b == self.U.find(new_id))
        self.worklist.append(new_id)
        # TODO new_id is one of `a` and `b` so setting it is redundant. remove
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
        if self.lookup_compression:
            canon_n = self.canonicalize(n)
            a = self.H.get(canon_n, None)
            if a is None:
                return None
            elif (canon_a := self.find(a)) != a:
                # `n`s canonical repr isn't mapped to a canonical e-class
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

    Returns list of all term IDs.
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


def plot_res(x_key, y_key, results, ax, curve_fit=lambda N: 1, label=None):
    X = list(map(lambda d: d[x_key], results))
    Y = list(map(lambda d: d[y_key] / curve_fit(d[x_key]), results))
    ax.plot(X, Y, label=label)
    ax.set(xlabel=x_key, ylabel=y_key)
    plt.legend()


def plot_asymptotics_on_linear():
    def run_with_strictness(strict):
        results = []
        for N in range(200):
            N = N + 50
            if N % 100 == 0:
              print("N =", N)
            egraph = EGraph(strict_rebuilding=strict)
            term_ids = setup_linear_graph(egraph, N)
            start_time = time.time()
            egraph.merge(term_ids[0], term_ids[-1])
            egraph.merge(term_ids[1], term_ids[-1])
            egraph.rebuild()
            rebuild_time = time.time() - start_time
            report = egraph.report()
            results.append(dict(report, N=N, rebuild_time=rebuild_time))
        return results

    lazy_res = run_with_strictness(False)
    # strict_res = run_with_strictness(True)

    fig, ax = plt.subplots()
    # N*log2(N+1) 
    # N*log2(log2(N+1)+1)
    # N*log2(log2(log2(log2(N+1)+1)+1)+1)
    plot_res('N', 'num_finds', lazy_res, ax, lambda N: N*log2(log2(log2(log2(log2(log2(log2(N+1)+1)+1)+1)+1)+1)+1), label='lazy')
    # plot_res('N', 'num_finds', lazy_res, ax, lambda N: N, label='lazy')
    # N**2
    # plot_res('N', 'num_finds', strict_res, ax, lambda N: N**2, label='strict')

    # fig, ax = plt.subplots()
    # plot_res('N', 'rebuild_time', lazy_res, ax, label='lazy')
    # plot_res('N', 'rebuild_time', strict_res, ax, label='strict')

    plt.axhline(y=0, color='r', linestyle='-')

    plt.show()



def setup_upside_down_T(egraph, width, depth):
    """
    Create graph with terms [f(f(...(a_1))), ..., f(f(...(a_w)))], where `f`
    is applied `depth` times and there are `width` such terms.

    Returns list of term IDs for the leaf nodes [a_1, ..., a_w].
    """
    leaf_ids = []
    for i in range(width):
        leaf = t(f'a{i}')
        curr = leaf
        for _ in range(depth):
            curr = t('f', curr)
        leaf_ids.append(egraph.add_term(leaf))
        egraph.add_term(curr)
    assert len(egraph.H) == width * (depth+1)
    egraph.reset_op_counts()
    return leaf_ids


def test_upside_down_T():
    def collect_single(width, depth, strict):
        egraph = EGraph(strict_rebuilding=strict)
        leaf_ids = setup_upside_down_T(egraph, width, depth)
        start_time = time.time()
        for leaf in leaf_ids[1:]:
            egraph.merge(leaf_ids[0], leaf)
        egraph.rebuild()
        rebuild_time = time.time() - start_time
        report = egraph.report()
        return dict(report, width=width, depth=depth, rebuild_time=rebuild_time)

    width = 10
    strict_res = []
    lazy_res = []
    for depth in range(1, 100):
        strict_res.append(collect_single(width, depth, True))
        lazy_res.append(collect_single(width, depth, False))

    fig, ax = plt.subplots()
    ax.set_title('varying depth with width fixed to 10')
    plot_res('depth', 'num_repairs', lazy_res, ax, label='lazy')
    plot_res('depth', 'num_repairs', strict_res, ax, label='strict')

    fig, ax = plt.subplots()
    ax.set_title('varying depth with width fixed to 10')
    plot_res('depth', 'num_finds', lazy_res, ax, label='lazy')
    plot_res('depth', 'num_finds', strict_res, ax, label='strict')

    fig, ax = plt.subplots()
    ax.set_title('varying depth with width fixed to 10')
    plot_res('depth', 'rebuild_time', lazy_res, ax, label='lazy')
    plot_res('depth', 'rebuild_time', strict_res, ax, label='strict')

    depth = 10
    strict_res = []
    lazy_res = []
    for width in range(1, 100):
        strict_res.append(collect_single(width, depth, True))
        lazy_res.append(collect_single(width, depth, False))

    fig, ax = plt.subplots()
    ax.set_title('varying width with depth fixed to 10')
    plot_res('width', 'num_repairs', lazy_res, ax, label='lazy')
    plot_res('width', 'num_repairs', strict_res, ax, label='strict')

    fig, ax = plt.subplots()
    ax.set_title('varying width with depth fixed to 10')
    plot_res('width', 'num_finds', lazy_res, ax, label='lazy')
    plot_res('width', 'num_finds', strict_res, ax, label='strict')

    fig, ax = plt.subplots()
    ax.set_title('varying width with depth fixed to 10')
    plot_res('width', 'rebuild_time', lazy_res, ax, label='lazy')
    plot_res('width', 'rebuild_time', strict_res, ax, label='strict')

    plt.show()


def main():
    # test_basic()
    # test_nelson_oppen_fig1()
    # test_nelson_oppen_fig2_strict()
    # test_nelson_oppen_fig2_lazy()

    # find_worst_input_for_linear()
    plot_asymptotics_on_linear()

    # test_upside_down_T()


if __name__ == '__main__':
    main()
