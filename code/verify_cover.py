"""Independently verify an OR-of-equality-matrices cover of DISJ_k.

Input format (as written by sa_cover.c): lines "M<t> u: <2^k labels>" and "M<t> v: <2^k labels>",
label -1 = unlabelled; a label is a separator S (bitmask) with rows x ⊆ S and columns y ⊆ ~S.
Checks that (1) every label is admissible and (2) the OR of the matrices equals DISJ_k exactly.
usage: python3 verify_cover.py covers/disj7_r8.txt
"""
import re, sys

U, V = {}, {}
for line in open(sys.argv[1]):
    m = re.match(r"M(\d+) ([uv]): (.*)", line)
    if m:
        (U if m.group(2) == "u" else V)[int(m.group(1))] = list(map(int, m.group(3).split()))
r, N = len(U), len(U[0])
k = N.bit_length() - 1
ok = all(U[t][x] == -1 or U[t][x] & x == x for t in range(r) for x in range(N))
ok &= all(V[t][y] == -1 or V[t][y] & y == 0 for t in range(r) for y in range(N))
for x in range(N):
    for y in range(N):
        hit = any(U[t][x] != -1 and U[t][x] == V[t][y] for t in range(r))
        ok &= hit == (x & y == 0)
print(f"DISJ_{k}: {r} equality matrices, cover {'VERIFIED' if ok else 'INVALID'}; r^(1/k) = {r ** (1 / k):.5f}")
