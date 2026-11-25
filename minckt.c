// Exhaustive search: is there a fan-in-2 circuit with exactly S gates computing F on 6 inputs?
// MODE 0: AND/OR only. MODE 1: AND/OR/NOT (NOT counts as a gate).
// Canonical form: gates in greedy-min-key topological order, so each gate either reads the
// previous gate or has a larger key than it. Minimal circuits never repeat a value, never make
// a constant, and use every gate and every essential input; the output is the last gate.
// usage: minckt MODE S P ID HI LO [SEED]  (process ID of P handles first-gate choices idx % P == ID;
//        SEED > 0 rotates the branch order randomly, still exhaustive)
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
typedef uint64_t u64;
#define N 6
static int S, MODE, P, ID;
static u64 F;
static u64 val[64]; static int uses[64], gop[64], ga[64], gb[64];
static int unused; static long long nodes; static long long firstIdx;
static u64 SEED, RS; static int PA[2048], PB[2048];
static u64 rnd(void) { RS ^= RS << 13; RS ^= RS >> 7; RS ^= RS << 17; return RS; }

static void print_circuit(int m) {
  printf("FOUND mode=%d size=%d:", MODE, S);
  for (int w = N; w < m; w++) {
    const char *o = gop[w] == 0 ? "and" : gop[w] == 1 ? "or" : "not";
    if (gop[w] == 2) printf(" w%d=%s(w%d)", w, o, ga[w]); else printf(" w%d=%s(w%d,w%d)", w, o, ga[w], gb[w]);
  }
  printf("\n"); fflush(stdout);
}

static int try_gate(int m, int op, int i, int j, u64 v, int prevkey) {
  int placed = m - N, r = S - placed - 1;  // gates left after this one
  int key = op * 4096 + i * 64 + (op == 2 ? 0 : j);
  if (placed > 0) {
    int readsPrev = (i == m - 1) || (op != 2 && j == m - 1);
    if (!readsPrev && key <= prevkey) return 0;
  }
  if (v == 0 || v == ~0ULL) return 0;
  if (r > 0 && v == F) return 0;
  for (int w = 0; w < m; w++) if (val[w] == v) return 0;
  int nu = unused + 1 - (uses[i] == 0) - (op != 2 && uses[j] == 0);
  if (nu > r + 1) return 0;
  if (placed == 0) { if ((firstIdx++ % P) != ID) return 0; }
  nodes++;
  if (r == 0) {
    if (v == F && nu == 1) { val[m] = v; gop[m] = op; ga[m] = i; gb[m] = j; print_circuit(m + 1); return 1; }
    return 0;
  }
  val[m] = v; gop[m] = op; ga[m] = i; gb[m] = j; uses[m] = 0;
  uses[i]++; if (op != 2) uses[j]++;
  if (r == 1) {
    // The last gate must read this new (unused) gate m and consume every unused wire.
    int q = -1, found = 0;
    if (nu == 2) { for (int w = 0; w < m; w++) if (uses[w] == 0) { q = w; break; } }
    for (int w = 0; w < m && !found; w++) {
      if (nu == 2 && w != q) continue;
      if ((v & val[w]) == F) { gop[m+1] = 0; ga[m+1] = w; gb[m+1] = m; found = 1; }
      else if ((v | val[w]) == F) { gop[m+1] = 1; ga[m+1] = w; gb[m+1] = m; found = 1; }
    }
    if (!found && nu == 1 && MODE == 1 && ~v == F) { gop[m+1] = 2; ga[m+1] = m; found = 1; }
    if (found) { print_circuit(m + 2); }
    uses[i]--; if (op != 2) uses[j]--;
    return found;
  }
  int save = unused; unused = nu;
  int ok = 0;
  int m2 = m + 1;
  // Every pair (a < b) once, in an order rotated by a random offset when SEED is set: the search
  // stays exhaustive, only the order changes, so different workers find a circuit sooner.
  int npair = m2 * (m2 - 1) / 2;
  int off = SEED ? (int)(rnd() % (u64)npair) : 0, flip = SEED ? (int)(rnd() & 1) : 0;
  for (int t = 0; t < npair && !ok; t++) {
    int p = (t + off) % npair, a = PA[p], b = PB[p];
    u64 v0 = val[a] & val[b], v1 = val[a] | val[b];
    ok = flip ? (try_gate(m2, 1, a, b, v1, key) || try_gate(m2, 0, a, b, v0, key))
              : (try_gate(m2, 0, a, b, v0, key) || try_gate(m2, 1, a, b, v1, key));
  }
  for (int a = 0; a < m2 && !ok && MODE == 1; a++) ok = try_gate(m2, 2, a, 0, ~val[a], key);
  unused = save; uses[i]--; if (op != 2) uses[j]--;
  return ok;
}

int main(int argc, char **argv) {
  MODE = atoi(argv[1]); S = atoi(argv[2]); P = atoi(argv[3]); ID = atoi(argv[4]);
  F = strtoull(argv[5], 0, 10) * 4294967296ULL + strtoull(argv[6], 0, 10);
  SEED = argc > 7 ? strtoull(argv[7], 0, 10) : 0; RS = SEED * 2654435761ULL + ID + 1;
  for (int b = 1, p = 0; b < 64 && p < 2048; b++) for (int a = 0; a < b && p < 2048; a++, p++) { PA[p] = a; PB[p] = b; }
  for (int i = 0; i < N; i++) { u64 x = 0; for (int r = 0; r < 64; r++) if (r >> i & 1) x |= 1ULL << r; val[i] = x; uses[i] = 0; }
  unused = 0;
  for (int i = 0; i < N; i++) { int ess = 0; for (int r = 0; r < 64; r++) if ((F >> r & 1) != (F >> (r ^ (1 << i)) & 1)) ess = 1; if (ess) unused++; else uses[i] = 1; }
  int ok = 0;
  for (int a = 0; a < N && !ok; a++) {
    for (int b = a + 1; b < N && !ok; b++)
      ok = try_gate(N, 0, a, b, val[a] & val[b], -1) || try_gate(N, 1, a, b, val[a] | val[b], -1);
    if (!ok && MODE == 1) ok = try_gate(N, 2, a, 0, ~val[a], -1);
  }
  printf("DONE mode=%d size=%d part=%d/%d found=%d nodes=%lld\n", MODE, S, ID, P, ok, nodes);
  return 0;
}
