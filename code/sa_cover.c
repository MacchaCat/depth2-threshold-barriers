/* Simulated annealing for equality covers of DISJ_k.
 *
 * State: for each matrix t < r, every row x carries a label S ⊇ x or none, every column y a label S ⊆ ~y or
 * none (separator labels, see eqcover.py, so every covered pair is automatically disjoint). A disjoint pair
 * (x,y) is covered by M_t iff both carry the same label in M_t. Objective: number of uncovered disjoint pairs.
 * Move: relabel one row or column in one matrix (uniform random admissible label or none); Metropolis rule.
 * usage: sa_cover k r seed [iters_millions] [T0] [T1]   -> prints the best objective; on success the cover.
 */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <stdint.h>

static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

int main(int argc, char **argv) {
  int k = atoi(argv[1]), r = atoi(argv[2]);
  rs = strtoull(argv[3], 0, 10) * 0x9E3779B97F4A7C15ULL + 12345;
  double iters = (argc > 4 ? atof(argv[4]) : 200) * 1e6;
  double T0 = argc > 5 ? atof(argv[5]) : 2.0, T1 = argc > 6 ? atof(argv[6]) : 0.05;
  int N = 1 << k, full = N - 1, NONE = -1;
  int *U = malloc(sizeof(int) * r * N), *V = malloc(sizeof(int) * r * N);
  int *cnt = calloc((size_t)N * N, sizeof(int));          /* cnt[x*N+y] = #matrices covering (x,y) */
  for (int i = 0; i < r * N; i++) U[i] = V[i] = NONE;
  long unc = 0;
  for (int x = 0; x < N; x++) for (int y = 0; y < N; y++) if (!(x & y)) unc++;
  long best = unc;
  int *BU = malloc(sizeof(int) * r * N), *BV = malloc(sizeof(int) * r * N);
  for (int i = 0; i < r * N; i++) { BU[i] = U[i]; BV[i] = V[i]; }
  /* set label of row (side 0) or column (side 1) z in matrix t to nw; updates cnt and returns the change in unc */
  #define SETLAB(t, side, z, nw) ({ long _d = 0; int _o = (side) ? V[(t) * N + (z)] : U[(t) * N + (z)]; \
    for (int w_ = 0; w_ < N; w_++) { if (w_ & (z)) continue; \
      int _x = (side) ? w_ : (z), _y = (side) ? (z) : w_; \
      int _l = (side) ? U[(t) * N + _x] : V[(t) * N + _y]; int *_c = &cnt[_x * N + _y]; \
      if (_o != NONE && _l == _o) { if (--*_c == 0) _d++; } \
      if ((nw) != NONE && _l == (nw)) { if ((*_c)++ == 0) _d--; } } \
    if (side) V[(t) * N + (z)] = (nw); else U[(t) * N + (z)] = (nw); unc += _d; _d; })
  /* WLOG M_0 covers (∅,∅): row ∅ and column ∅ of M_0 share one label at all times (moved together) */
  { long d0 = SETLAB(0, 0, 0, 0); d0 += SETLAB(0, 1, 0, 0); (void)d0; }
  if (unc < best) best = unc;
  /* random admissible label: superset of x (rows) or subset of ~y (columns), or NONE w.p. 1/16 */
  for (double it = 0; it < iters; it++) {
    double T = T0 * pow(T1 / T0, it / iters);
    int t = rnd() % r, side = rnd() & 1, z = rnd() % N, nw;
    int tied = (t == 0 && z == 0);
    if (tied) nw = (int)(rnd() & (uint64_t)full);
    else if ((rnd() & 15) == 0) nw = NONE;
    else nw = side ? (int)(rnd() & (uint64_t)(full & ~z)) : (z | (int)(rnd() & (uint64_t)(full & ~z)));
    int old = side ? V[t * N + z] : U[t * N + z];
    if (nw == old) continue;
    long d;
    if (tied) { d = SETLAB(0, 0, 0, nw); d += SETLAB(0, 1, 0, nw); }
    else d = SETLAB(t, side, z, nw);
    if (!(d <= 0 || urand() < exp(-d / T))) {   /* reject: revert */
      if (tied) { SETLAB(0, 0, 0, old); SETLAB(0, 1, 0, old); }
      else SETLAB(t, side, z, old);
    }
    if (unc < best) {
      best = unc;
      for (int i = 0; i < r * N; i++) { BU[i] = U[i]; BV[i] = V[i]; }
      if (best == 0) break;
    }
  }
  printf("k=%d r=%d best_uncovered=%ld\n", k, r, best);
  U = BU; V = BV;
  if (best > 0 && best <= 20) {      /* list the uncovered pairs of the best state */
    printf("uncovered:");
    for (int x = 0; x < N; x++) for (int y = 0; y < N; y++) {
      if (x & y) continue;
      int hit = 0;
      for (int t = 0; t < r; t++) if (U[t * N + x] != NONE && U[t * N + x] == V[t * N + y]) hit = 1;
      if (!hit) printf(" (%d,%d)", x, y);
    }
    printf("\n");
  }
  if (best == 0) {
    /* independent verification */
    int ok = 1;
    for (int x = 0; x < N && ok; x++) for (int y = 0; y < N; y++) {
      int hit = 0;
      for (int t = 0; t < r; t++) if (U[t * N + x] != NONE && U[t * N + x] == V[t * N + y]) hit = 1;
      if (hit != !(x & y)) { ok = 0; break; }
    }
    printf("FOUND verified=%d\n", ok);
    for (int t = 0; t < r; t++) {
      printf("M%d u:", t); for (int x = 0; x < N; x++) printf(" %d", U[t * N + x]); printf("\n");
      printf("M%d v:", t); for (int y = 0; y < N; y++) printf(" %d", V[t * N + y]); printf("\n");
    }
  }
  return 0;
}
