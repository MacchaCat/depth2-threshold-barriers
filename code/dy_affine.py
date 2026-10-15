"""Exact check of the Diamond–Yehudayoff conjecture for small d.

Claim checked: every affine subspace V of R^{2d} with V ∩ {0,1}^{2d} ⊆ D_d (all points are disjoint pairs)
contains at most 2^d cube points. This is equivalent to the hyperplane version over ALL real weights:
S = H ∩ cube ⊆ D implies S = aff(S) ∩ cube, and conversely a generic hyperplane through aff(S) avoids the
remaining cube points. We enumerate every affinely closed contained S by depth-first closure.
Arithmetic is exact (rank over the rationals via fraction-free elimination on small integer vectors).
usage: dy_affine.py d
"""
import sys
from itertools import product
from fractions import Fraction

d = int(sys.argv[1]); n = 2 * d
cube = [tuple(p) for p in product((0, 1), repeat=n)]
isD = {p: all(not (p[i] and p[d + i]) for i in range(d)) for p in cube}
Dpts = [p for p in cube if isD[p]]

def rank(vecs):
    rows = [list(map(Fraction, v)) for v in vecs]; r = 0
    if not rows: return 0
    m = len(rows[0])
    for c in range(m):
        piv = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        if piv is None: continue
        rows[r], rows[piv] = rows[piv], rows[r]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c] / rows[r][c]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[r])]
        r += 1
    return r

def closure(S):
    S = list(S); base = S[0]
    dirs = [tuple(a - b for a, b in zip(p, base)) for p in S[1:]]
    r = rank(dirs)
    # reduce dirs to an independent set for faster membership tests
    basis = []
    for v in dirs:
        if rank(basis + [v]) > len(basis): basis.append(v)
    out = []
    for p in cube:
        v = tuple(a - b for a, b in zip(p, base))
        if rank(basis + [v]) == len(basis): out.append(p)
    return frozenset(out), len(basis)

seen = {}; best = 0; bestS = None
stack = [closure([p]) for p in Dpts]
while stack:
    S, dim = stack.pop()
    if S in seen: continue
    if not all(isD[p] for p in S): seen[S] = False; continue
    seen[S] = True
    if len(S) > best:
        best = len(S); bestS = (S, dim)
    for p in Dpts:
        if p not in S:
            T = closure(list(S) + [p])
            if T[0] not in seen: stack.append(T)
contained = sum(1 for v in seen.values() if v)
print(f"d={d}: {contained} contained affinely closed sets explored; max |S| = {best} (2^d = {2**d}); "
      f"an extremal S has affine dim {bestS[1]}")
