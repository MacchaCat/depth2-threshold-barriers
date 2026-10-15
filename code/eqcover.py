"""Equality-cover number of the Disjointness matrix.

cov(k) = least r such that the ones of DISJ_k (pairs x, y ⊆ [k] with x ∩ y = ∅) are the union of the ones
of r equality matrices M_t[x, y] = [u_t(x) = v_t(y)] whose ones lie inside DISJ_k. Such an OR is a weak
equality-rank decomposition (all coefficients 1), so weak-eq-rank(DISJ_k) ≤ cov(k); Williams (TR24-142, §6)
found cov(6) ≤ 6, giving an O~(n · 6^{d/6}) OV algorithm, and cov(k) ≤ r gives O~(n · r^{d/k}).

Encoding. A label of M_t is a block R × C of ones; enlarging it to (all subsets of S) × (all subsets of the
complement of S), where S = union of R, keeps it inside DISJ_k, and two labels with the same S can be merged.
So WLOG labels are separators S ⊆ [k]: row x may take label S only if x ⊆ S, column y only if S ∩ y = ∅,
each row/column takes at most one label per matrix, and every disjoint (x, y) must share a label in some M_t.
usage: eqcover.py k r [solver] [--break]   -> prints SAT + the decomposition, or UNSAT
--break adds value-precedence symmetry breaking over the r interchangeable matrices (exact cov literals).
"""
import sys, itertools
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool


def build(k, r, sym_break):
    N = 1 << k
    full = N - 1
    pool = IDPool()
    A = lambda t, x, S: pool.id(("a", t, x, S))
    B = lambda t, y, S: pool.id(("b", t, y, S))
    supersets = [[S for S in range(N) if S & x == x] for x in range(N)]
    clauses = []
    for t in range(r):
        for x in range(N):
            lits = [A(t, x, S) for S in supersets[x]]
            if len(lits) > 1:
                clauses += CardEnc.atmost(lits, 1, vpool=pool, encoding=EncType.seqcounter).clauses
        for y in range(N):
            lits = [B(t, y, S) for S in supersets[0] if S & y == 0]
            if len(lits) > 1:
                clauses += CardEnc.atmost(lits, 1, vpool=pool, encoding=EncType.seqcounter).clauses
    # anchor order for symmetry breaking: (∅,∅), then complementary pairs (x, x̄) by |x|, then the rest
    pairs = [(x, y) for x in range(N) for y in range(N) if x & y == 0]
    pairs.sort(key=lambda p: (p != (0, 0), (p[0] | p[1]) != full, bin(p[0]).count("1"), p))
    C = lambda j, t: pool.id(("cov", j, t))
    for j, (x, y) in enumerate(pairs):
        free = full & ~(x | y)
        # S ranges over x ∪ T for T ⊆ free
        ws = [[] for _ in range(r)]
        T = free
        while True:
            S = x | T
            for t in range(r):
                w = pool.id(("w", t, x, y, S))
                clauses.append([-w, A(t, x, S)])
                clauses.append([-w, B(t, y, S)])
                if sym_break:                      # w <-> a ∧ b, so cov(j,t) is exact
                    clauses.append([w, -A(t, x, S), -B(t, y, S)])
                ws[t].append(w)
            if T == 0:
                break
            T = (T - 1) & free
        for t in range(r):                         # cov(j,t) <-> OR_S w
            clauses.append([-C(j, t)] + ws[t])
            for w in ws[t]:
                clauses.append([-w, C(j, t)])
        clauses.append([C(j, t) for t in range(r)])
    if sym_break:
        # Matrices are interchangeable. Let m(j) = least matrix covering anchor j. Relabel matrices in order
        # of first appearance in m(0), m(1), ...; then m(j) = t >= 1 forces some i < j with m(i) = t - 1.
        G = lambda j, t: pool.id(("g", j, t))     # m(j) = t
        Z = lambda j, t: pool.id(("none", j, t))  # no matrix < t covers j
        P = lambda j, t: pool.id(("seen", j, t))  # some i <= j has m(i) = t
        for j in range(len(pairs)):
            clauses.append([Z(j, 0)])
            for t in range(r):
                if t + 1 < r:   # Z(j,t+1) <-> Z(j,t) ∧ ¬C(j,t)
                    clauses += [[-Z(j, t + 1), Z(j, t)], [-Z(j, t + 1), -C(j, t)], [Z(j, t + 1), -Z(j, t), C(j, t)]]
                clauses += [[-G(j, t), C(j, t)], [-G(j, t), Z(j, t)], [G(j, t), -C(j, t), -Z(j, t)]]
                prev = [P(j - 1, t)] if j else []
                clauses += [[-P(j, t), G(j, t)] + prev, [P(j, t), -G(j, t)]] + ([[P(j, t), -P(j - 1, t)]] if j else [])
                if t >= 1:
                    clauses.append([-G(j, t)] + ([P(j - 1, t - 1)] if j else []))
        # Coordinates are interchangeable too. Anchor 0 is (∅,∅), so m(0) = 0 and row ∅ of M_0 carries a label S_0;
        # permuting coordinates (which preserves the anchor order up to ties that the matrix relabelling absorbs,
        # since m(0) = 0 regardless) makes S_0 an initial segment {0, ..., s-1}.
        segs = {(1 << s) - 1 for s in range(k + 1)}
        for S in range(N):
            if S not in segs:
                clauses.append([-A(0, 0, S)])
    return pool, clauses


def decode(model, pool, k, r):
    N = 1 << k
    pos = set(l for l in model if l > 0)
    U = [[None] * N for _ in range(r)]
    V = [[None] * N for _ in range(r)]
    for t in range(r):
        for x in range(N):
            for S in range(N):
                if S & x == x and pool.obj2id.get(("a", t, x, S)) in pos:
                    U[t][x] = S
        for y in range(N):
            for S in range(N):
                if S & y == 0 and pool.obj2id.get(("b", t, y, S)) in pos:
                    V[t][y] = S
    return U, V


def verify(U, V, k):
    N = 1 << k
    for x in range(N):
        for y in range(N):
            hit = any(U[t][x] is not None and U[t][x] == V[t][y] for t in range(len(U)))
            if hit != (x & y == 0):
                return False
    return True


if __name__ == "__main__":
    k, r = int(sys.argv[1]), int(sys.argv[2])
    name = sys.argv[3] if len(sys.argv) > 3 and not sys.argv[3].startswith("--") else "cadical195"
    pool, clauses = build(k, r, "--break" in sys.argv)
    print(f"k={k} r={r} vars={pool.top} clauses={len(clauses)}", flush=True)
    with Solver(name=name, bootstrap_with=clauses) as s:
        ok = s.solve()
        if ok:
            U, V = decode(s.get_model(), pool, k, r)
            print(f"SAT  verified={verify(U, V, k)}")
            for t in range(r):
                print(f"M{t}: u={U[t]}\n    v={V[t]}")
        else:
            print("UNSAT")
