#!/usr/bin/env python
# -*- coding: utf-8 -*-

"""This module implements an union find or disjoint set data structure.

An union find data structure can keep track of a set of elements into a number
of disjoint (nonoverlapping) subsets. That is why it is also known as the
disjoint set data structure. Mainly two useful operations on such a data
structure can be performed. A *find* operation determines which subset a
particular element is in. This can be used for determining if two
elements are in the same subset. An *union* Join two subsets into a
single subset.

The complexity of these two operations depend on the particular implementation.
It is possible to achieve constant time (O(1)) for any one of those operations
while the operation is penalized. A balance between the complexities of these
two operations is desirable and achievable following two enhancements:

1.  Using union by rank -- always attach the smaller tree to the root of the
    larger tree.
2.  Using path compression -- flattening the structure of the tree whenever
    find is used on it.

complexity:
    * find -- :math:`O(\\alpha(N))` where :math:`\\alpha(n)` is
      `inverse ackerman function
      <http://en.wikipedia.org/wiki/Ackermann_function#Inverse>`_.
    * union -- :math:`O(\\alpha(N))` where :math:`\\alpha(n)` is
      `inverse ackerman function
      <http://en.wikipedia.org/wiki/Ackermann_function#Inverse>`_.

"""


class UnionFind:
    """An implementation of union find data structure.
    It uses weighted quick union by rank with path compression.
    """

    def __init__(self):
        """Initialize an empty union find object."""
        self.ids = []
        self.count = 0
        self.ranks = []
        self.num_finds = 0

    def add_set(self):
        new_id = len(self.ids)
        self.ids.append(new_id)
        self.count += 1
        self.ranks.append(0)
        return new_id

    def find(self, p):
        """Find the set identifier for the item p."""
        assert type(p) == int

        if p == self.ids[p]:
            # only count in the base case, so we don't overcount with recursive
            # calls
            self.num_finds += 1
            return p
        else:
            res = self.find(self.ids[p])
            self.ids[p] = res
            return res

    def count(self):
        """Return the number of distinct sets."""
        return self.count

    def connected(self, p, q):
        """Check if the items p and q are on the same set or not."""
        return self.find(p) == self.find(q)

    def union(self, p, q):
        """Combine sets containing p and q into a single set."""

        i = self.find(p)
        j = self.find(q)
        if i == j:
            return i

        self.count -= 1
        if self.ranks[i] < self.ranks[j]:
            self.ids[i] = j
            res = j
        elif self.ranks[i] > self.ranks[j]:
            self.ids[j] = i
            res = i
        else:
            self.ids[j] = i
            self.ranks[i] += 1
            res = i
        return res

    def __str__(self):
        """String representation of the union find object."""
        return " ".join([str(x) for x in self.ids])

    def __repr__(self):
        """Representation of the union find object."""
        return "UnionFind(" + str(self) + ")"

if __name__ == "__main__":
    print("Union find data structure.")
    N = int(raw_input("Enter number of items: "))
    uf = UnionFind(N)
    print("Enter a sequence of space separated pairs of integers: ")
    while True:
        try:
            p, q = [int(x) for x in raw_input().split()]
            uf.union(p, q)
        except:
            break

    print(str(uf.count()) + " components: " + str(uf))
