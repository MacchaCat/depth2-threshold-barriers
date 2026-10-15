"""mu(d) = max number of ones of a single equality matrix inside DISJ_d, by MILP.
Labels are separators S (rows x ⊆ S, columns y ⊆ complement of S; see eqcover.py). Compare with the
entropy bound mu(d) <= (3*sqrt(3)/2)^d.  usage: eqmax.py d"""
import sys
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix

d = int(sys.argv[1]); N = 1 << d; full = N - 1
av = {}; bv = {}; wv = []
for x in range(N):
    for S in range(N):
        if S & x == x: av[(x, S)] = len(av)
na = len(av)
for y in range(N):
    for S in range(N):
        if S & y == 0: bv[(y, S)] = na + len(bv)
nb = len(bv)
for x in range(N):
    for y in range(N):
        if x & y: continue
        free = full & ~(x | y); T = free
        while True:
            wv.append((x, y, x | T))
            if T == 0: break
            T = (T - 1) & free
nv = na + nb + len(wv)
rows = N + N + 2 * len(wv)
A = lil_matrix((rows, nv)); lo = np.full(rows, -np.inf); hi = np.zeros(rows); r = 0
for x in range(N):            # each row at most one label
    for S in range(N):
        if S & x == x: A[r, av[(x, S)]] = 1
    hi[r] = 1; r += 1
for y in range(N):
    for S in range(N):
        if S & y == 0: A[r, bv[(y, S)]] = 1
    hi[r] = 1; r += 1
for j, (x, y, S) in enumerate(wv):   # w <= a, w <= b
    A[r, na + nb + j] = 1; A[r, av[(x, S)]] = -1; r += 1
    A[r, na + nb + j] = 1; A[r, bv[(y, S)]] = -1; r += 1
c = np.zeros(nv); c[na + nb:] = -1
res = milp(c, constraints=LinearConstraint(A.tocsr(), lo, hi), integrality=np.ones(nv), bounds=Bounds(0, 1),
           options={"time_limit": 3000})
print(f"d={d} mu={-res.fun:.0f} (status {res.status}, bound {(-res.mip_dual_bound if hasattr(res,'mip_dual_bound') and res.mip_dual_bound is not None else float('nan')):.1f})"
      f"  entropy bound={(3*3**0.5/2)**d:.1f}  3^d={3**d}  => cover >= {3**d/(-res.fun):.2f}")
