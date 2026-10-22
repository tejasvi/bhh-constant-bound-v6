/* w3ind_auto.h: sliding-window encoding (W = 3) of the value of the window-3 specification (its Section 2), written from
   its definition:
     H_3 = sure edges between sorted indices at distance 1, 2 or 3; u(H) = #{v : deg_H(v) < 2};
     val(H) = 1{H connected} * max(0, 1 - u(H)/2), returned doubled (0, 1, 2).
   State after placing y_0..y_i: the window (the last min(i+1, 3) points, oldest first), the partition of the window points
   by the components of H_3[y_0..y_i] (invariant: every component meets the window), their degrees capped at 2, and
   u = number of points that left the window with degree < 2 (u >= 2: dead).
   Step (add q = y_{i+1}; inputs N = edge to y_i, S = edge to y_{i-1}, T = edge to y_{i-2}): add the edges, then the oldest
   point leaves if the window held 3 points; its degree is final (its partners are within sorted distance 3), and its
   component must contain a point of the new window (later points join only window points), otherwise dead.
   States are enumerated by breadth-first search from the start state and numbered in that order. */
#ifndef W3IND_AUTO_H
#define W3IND_AUTO_H
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct { int n, lab[3], deg[3], u; } a3_st;      /* window oldest first: w[0..n-1] */

static int a3_key(const a3_st *s) {                       /* canonical labels assumed */
  int k = s->n;
  for (int j = 0; j < 3; j++) k = k * 4 + (j < s->n ? s->lab[j] : 3);
  for (int j = 0; j < 3; j++) k = k * 3 + (j < s->n ? s->deg[j] : 0);
  return k * 2 + s->u;
}
static void a3_canon(a3_st *s) {
  int map[16]; for (int j = 0; j < 16; j++) map[j] = -1;
  int nx = 0;
  for (int j = 0; j < s->n; j++) { int l = s->lab[j]; if (map[l] < 0) map[l] = nx++; s->lab[j] = map[l]; }
}
static int cap2(int x) { return x > 2 ? 2 : x; }
/* one step; returns 0 if dead */
static int a3_step_st(const a3_st *s, int N, int S, int T, a3_st *o) {
  int n = s->n, lab[4], deg[4];
  for (int j = 0; j < n; j++) { lab[j] = s->lab[j]; deg[j] = s->deg[j]; }
  lab[n] = 8; deg[n] = 0;                                  /* new point q, fresh label */
  int e[3] = {N, S, T};                                    /* partners: w[n-1], w[n-2], w[n-3] */
  for (int a = 0; a < 3; a++) {
    if (!e[a]) continue;
    int p = n - 1 - a;
    if (p < 0) return -1;                                  /* edge to a point that does not exist: invalid input */
    deg[p]++; deg[n]++;
    int lp = lab[p], lq = lab[n];
    if (lp != lq) for (int j = 0; j <= n; j++) if (lab[j] == lq) lab[j] = lp;
  }
  for (int j = 0; j <= n; j++) deg[j] = cap2(deg[j]);
  int u = s->u, start = 0;
  if (n == 3) {                                            /* the oldest point leaves */
    if (deg[0] < 2) u++;
    if (u >= 2) return 0;
    int alive = 0; for (int j = 1; j <= 3; j++) if (lab[j] == lab[0]) alive = 1;
    if (!alive) return 0;
    start = 1;
  }
  o->n = n + 1 - start; o->u = u;
  for (int j = 0; j < o->n; j++) { o->lab[j] = lab[start + j]; o->deg[j] = deg[start + j]; }
  a3_canon(o);
  return 1;
}
/* doubled closing value of a state after the last point */
static int a3_close_st(const a3_st *s) {
  for (int j = 1; j < s->n; j++) if (s->lab[j] != s->lab[0]) return 0;
  int ut = s->u; for (int j = 0; j < s->n; j++) if (s->deg[j] < 2) ut++;
  return ut >= 2 ? 0 : 2 - ut;
}

/* enumerated automaton */
#define A3_MAXST 512
static int a3_nst = 0, a3_start = 0;
static a3_st a3_states[A3_MAXST];
static int a3_trans[A3_MAXST][2][2][2];                    /* -1 dead or invalid */
static int a3_close2[A3_MAXST];
static int a3_find(const a3_st *s) {
  int k = a3_key(s);
  for (int i = 0; i < a3_nst; i++) if (a3_key(&a3_states[i]) == k) return i;
  return -1;
}
static void a3_build(void) {
  a3_st s0 = {1, {0, 0, 0}, {0, 0, 0}, 0};
  a3_nst = 0; a3_states[a3_nst++] = s0; a3_start = 0;
  for (int i = 0; i < a3_nst; i++) {
    for (int N = 0; N < 2; N++) for (int S = 0; S < 2; S++) for (int T = 0; T < 2; T++) {
      a3_st o; int r = a3_step_st(&a3_states[i], N, S, T, &o);
      if (r <= 0) { a3_trans[i][N][S][T] = -1; continue; }
      int j = a3_find(&o);
      if (j < 0) { if (a3_nst >= A3_MAXST) { fprintf(stderr, "automaton too large\n"); exit(7); } j = a3_nst; a3_states[a3_nst++] = o; }
      a3_trans[i][N][S][T] = j;
    }
    a3_close2[i] = a3_close_st(&a3_states[i]);
  }
}
#endif
