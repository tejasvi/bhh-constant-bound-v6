/* chk_ck14.c -- independent rigorous checker (FLINT/arb ball arithmetic, OpenMP) for the box-integration lower bounds on the
 * Dong-Cao terms C_k produced by the search program box_ck14.c (from a snapshot of it).
 *
 *   usage: chk_ck14 K W0 WF EPS [--shard LO HI] [--ninit N]   (same arguments as box_ck14; g = p - D only)
 *
 * Part A (lines marked "verbatim box_ck14") is a verbatim copy of the float search code (snapshot box_ck14_snapshot.c): it re-runs EXACTLY the same box
 * recursion (same splits, same prunes/drops, same scored leaves) and its float per-leaf values.  The only additions in
 * Part A are observation-only lines marked CHK (they record float quantities and call chk_leaf() at the two places where
 * box_ck14 adds a scored leaf to its total).  Dropping/pruning never needs rigour (the integrand is >= 0).
 *
 * Part B is written from BOUNDS.md (not from the float formulas): for every scored leaf it recomputes, in arb ball
 * arithmetic, a rigorous lower bound of the leaf's contribution int_Q r2 g(G_1(y)) A(y)^{-(k-1/2)} dx:
 *   B1 own g table (2g = 2p - n1, p = minimum path cover by brute force over vertex orders), completions by enumeration;
 *   B2 edge classes from the exact dyadic corners (arf, exact);
 *   B3 union area A(c) and grad A(c) at the box centre: exposed arcs via exact proxy endpoints on a proxy circle of
 *      length T' (a double near 2 pi), evaluated in arb, plus a rigorous symmetric-difference error term;
 *   B4 Lemma V remainder with the tangential cap min(|w|/d^-, pi) (c_r, c0, vertex pruning only when the arb test certainly
 *      holds, Rmax, E r, E r^2 with the box_ck14 moment bounds); B3e enlarged-disk union area for boxes with d^- = 0 (3e);
 *   B5 3b bracket (corrected: expansion at A(c), (h0/2) Er, Minkowski); 3c joint-state extras sum_s (g_s - gmin) EV(P_lo(E_s))
 *      over single undetermined edges and pairs (staircase bounds from exact trapezoid CDFs, products for vertex-disjoint
 *      pairs, Frechet otherwise), EV(q) = max(q fmin_pt, val - (1-q) fmax_pt); 3d gmin EV(P(xi_j <= xi_{j+1}));
 *   B6 rigorous summation and the prefactor 2 pi Gamma(k-1/2) (k-2)!/k! in arb.
 * See README in this directory.
 */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <omp.h>
#include <flint/flint.h>
#include <flint/arf.h>
#include <flint/mag.h>
#include <flint/arb.h>
#include <flint/fmpz.h>

/* ======================================================================================================================
 * Part A: verbatim box_ck14 (snapshot of box_ck14.c, lines 27-399, sha256 6feb4deb...), plus CHK observation lines.
 * ==================================================================================================================== */
#define KMAX 8
#define DMAX (2 * KMAX - 3)
#define PMAX (KMAX * (KMAX - 1) / 2)
static int k, m, use_q = 0, npairs, pi_[PMAX], pj_[PMAX];
static double W0, WF, EPS, s_exp, PREF;
static signed char *g2tab, *gmin3, *gmax3;
static long long pow3[PMAX + 1];

/* ---------------- geometry ---------------- */
static double union_area_grad(const double *x, const double *y, double *gx, double *gy) {
    double total = 0;
    for (int i = 0; i < k; i++) {
        gx[i] = 0; gy[i] = 0;
        double L[2 * KMAX], H[2 * KMAX]; int q = 0, covered = 0;
        for (int j = 0; j < k; j++) {
            if (j == i) continue;
            double dx = x[j] - x[i], dy = y[j] - y[i], d = sqrt(dx * dx + dy * dy);
            if (d >= 2) continue;
            if (d == 0) { if (j < i) { covered = 1; break; } else continue; }
            double phi = atan2(dy, dx), a = acos(d / 2);
            double a0 = phi - a, b0 = phi + a;
            while (a0 < 0) { a0 += 2 * M_PI; b0 += 2 * M_PI; }
            while (a0 >= 2 * M_PI) { a0 -= 2 * M_PI; b0 -= 2 * M_PI; }
            if (b0 <= 2 * M_PI) { L[q] = a0; H[q] = b0; q++; }
            else { L[q] = a0; H[q] = 2 * M_PI; q++; L[q] = 0; H[q] = b0 - 2 * M_PI; q++; }
        }
        if (covered) continue;
        for (int s = 1; s < q; s++) {
            double a0 = L[s], b0 = H[s]; int r = s - 1;
            while (r >= 0 && L[r] > a0) { L[r + 1] = L[r]; H[r + 1] = H[r]; r--; }
            L[r + 1] = a0; H[r + 1] = b0;
        }
        double cur = 0;
        for (int s = 0; s <= q; s++) {
            double a0 = (s < q) ? L[s] : 2 * M_PI;
            if (a0 > cur) {
                double sa = sin(cur), sb = sin(a0), ca = cos(cur), cb = cos(a0);
                total += 0.5 * ((a0 - cur) + x[i] * (sb - sa) - y[i] * (cb - ca));
                gx[i] += sb - sa; gy[i] += ca - cb;
            }
            if (s < q && H[s] > cur) cur = H[s];
        }
    }
    return total;
}

/* ---------------- graphs ---------------- */
static int components(const int *adj, int mask) {
    int seen = 0, cc = 0;
    for (int v = 0; v < k; v++) {
        if (!((mask >> v) & 1) || ((seen >> v) & 1)) continue;
        cc++;
        int fr = 1 << v; seen |= fr;
        while (fr) { int u = __builtin_ctz(fr); fr &= fr - 1; int nb = adj[u] & mask & ~seen; seen |= nb; fr |= nb; }
    }
    return cc;
}
static int min_path_cover(const int *adj) {
    static int hp[1 << KMAX], pc[1 << KMAX];
    int full = (1 << k) - 1;
    for (int mask = 1; mask <= full; mask++) {
        if ((mask & (mask - 1)) == 0) { hp[mask] = mask; continue; }
        int ends = 0;
        for (int v = 0; v < k; v++) if ((mask >> v) & 1) { int rest = mask & ~(1 << v); if (hp[rest] & adj[v]) ends |= 1 << v; }
        hp[mask] = ends;
    }
    pc[0] = 0;
    for (int mask = 1; mask <= full; mask++) {
        int low = mask & -mask, best = 99;
        for (int sub = mask; sub; sub = (sub - 1) & mask) {
            if (!(sub & low) || !hp[sub]) continue;
            int c = 1 + pc[mask & ~sub]; if (c < best) best = c;
        }
        pc[mask] = best;
    }
    return pc[full];
}
static int g2_of(const int *adj) {                 /* 2g */
    int full = (1 << k) - 1;
    if (components(adj, full) != 1) return 0;
    int n1 = 0; for (int i = 0; i < k; i++) if (__builtin_popcount(adj[i]) == 1) n1++;
    int val;
    if (use_q) {
        int q = 1; if ((n1 + 1) / 2 > q) q = (n1 + 1) / 2;
        for (int S = 1; S < full; S++) { int c = components(adj, full & ~S) - __builtin_popcount(S); if (c > q) q = c; }
        val = q;
    } else val = min_path_cover(adj);
    return 2 * val - n1;
}
static void build_tables(void) {
    npairs = 0;
    for (int i = 0; i < k; i++) for (int j = i + 1; j < k; j++) { pi_[npairs] = i; pj_[npairs] = j; npairs++; }
    long long ng = 1LL << npairs;
    g2tab = malloc(ng);
    for (long long e = 0; e < ng; e++) {
        int adj[KMAX] = {0};
        for (int p = 0; p < npairs; p++) if ((e >> p) & 1) { adj[pi_[p]] |= 1 << pj_[p]; adj[pj_[p]] |= 1 << pi_[p]; }
        g2tab[e] = (signed char)g2_of(adj);
    }
    pow3[0] = 1; for (int p = 1; p <= npairs; p++) pow3[p] = pow3[p - 1] * 3;
    long long n3 = pow3[npairs];
    gmin3 = malloc(n3); gmax3 = malloc(n3);
    for (long long idx = 0; idx < n3; idx++) {
        long long t = idx, e = 0; int firstu = -1;
        for (int p = 0; p < npairs; p++) { int st = t % 3; t /= 3; if (st == 1) e |= 1LL << p; else if (st == 2 && firstu < 0) firstu = p; }
        if (firstu < 0) { gmin3[idx] = gmax3[idx] = g2tab[e]; continue; }
        long long i0 = idx - 2 * pow3[firstu], i1 = idx - pow3[firstu];
        gmin3[idx] = gmin3[i0] < gmin3[i1] ? gmin3[i0] : gmin3[i1];
        gmax3[idx] = gmax3[i0] > gmax3[i1] ? gmax3[i0] : gmax3[i1];
    }
}

/* ---------------- P(|U_i - U_j| <= 1) staircase bounds ---------------- */
static double cdf_diff(double a, double b, double c, double d, double z) {   /* P(X - Y <= z), X~U[a,b], Y~U[c,d] */
    if (b - a <= 0 && d - c <= 0) return (a - c <= z) ? 1.0 : 0.0;
    if (b - a <= 0) { double t = (d - (a - z)) / (d - c); return t < 0 ? 0 : (t > 1 ? 1 : t); }
    if (d - c <= 0) { double t = (c + z - a) / (b - a); return t < 0 ? 0 : (t > 1 ? 1 : t); }
    double pts[4]; int np = 0;
    pts[np++] = a;
    double c1 = c + z, d1 = d + z;
    if (c1 > a && c1 < b) pts[np++] = c1;
    if (d1 > a && d1 < b) pts[np++] = d1;
    pts[np++] = b;
    if (np == 4 && pts[1] > pts[2]) { double t = pts[1]; pts[1] = pts[2]; pts[2] = t; }
    double tot = 0;
    for (int s = 0; s + 1 < np; s++) {
        double x0 = pts[s], x1 = pts[s + 1];
        double f0 = d - fmin(fmax(x0 - z, c), d), f1 = d - fmin(fmax(x1 - z, c), d);
        tot += 0.5 * (f0 + f1) * (x1 - x0);
    }
    double p = tot / ((b - a) * (d - c));
    return p < 0 ? 0 : (p > 1 ? 1 : p);
}
#define NSTRIP 8
static void prob_unit(double xli, double xhi, double yli, double yhi, double xlj, double xhj, double ylj, double yhj,
                      double *pin, double *pout) {
    double zx0 = xli - xhj, zx1 = xhi - xlj, in = 0, outer = 0;
    if (zx1 <= zx0) {                                  /* both x-degenerate: Z_x is a point */
        double ax = fabs(zx0);
        if (ax < 1) { double t = sqrt(1 - ax * ax);
            double p = cdf_diff(yli, yhi, ylj, yhj, t) - cdf_diff(yli, yhi, ylj, yhj, -t); if (p < 0) p = 0; in = p; outer = p; }
        *pin = in; *pout = 1 - outer; return;
    }
    double F[NSTRIP + 1];
    for (int t = 0; t <= NSTRIP; t++) F[t] = cdf_diff(xli, xhi, xlj, xhj, zx0 + (zx1 - zx0) * t / NSTRIP);
    for (int t = 0; t < NSTRIP; t++) {
        double x0 = zx0 + (zx1 - zx0) * t / NSTRIP, x1 = zx0 + (zx1 - zx0) * (t + 1) / NSTRIP;
        double px = F[t + 1] - F[t]; if (px <= 0) continue;
        double amax = fmax(fabs(x0), fabs(x1)), amin = (x0 <= 0 && x1 >= 0) ? 0 : fmin(fabs(x0), fabs(x1));
        if (amax < 1) { double yt = sqrt(1 - amax * amax);
            double p = cdf_diff(yli, yhi, ylj, yhj, yt) - cdf_diff(yli, yhi, ylj, yhj, -yt); if (p > 0) in += px * p; }
        if (amin < 1) { double Yt = sqrt(1 - amin * amin);
            double p = cdf_diff(yli, yhi, ylj, yhj, Yt) - cdf_diff(yli, yhi, ylj, yhj, -Yt); if (p > 0) outer += px * p; }
    }
    *pin = in; *pout = 1 - outer < 0 ? 0 : 1 - outer;
}

/* ---------------- boxes ---------------- */
typedef struct { double lo[DMAX], hi[DMAX]; } Box;
typedef struct { double lb, mid, extra, voldrop, lossdrop, l_int, l_bnd, l_str, l_coi; long long scored, dropped, visited; } Acc;
/* CHK: float information handed to the rigorous leaf evaluation (used only for the comparison diagnostics) */
typedef struct { double flt, A, Er, sqrtEr2, Rmax, val, tmin; int straddle, spair, gmin, gmax, enl; long long pres, und;
                 int nv[PMAX]; } FInfo;   /* CHK */
static void chk_leaf(const Box *b, const FInfo *fi);   /* CHK */

static inline double ivmin(double al, double ah, double bl, double bh) { if (ah < bl) return bl - ah; if (bh < al) return al - bh; return 0; }
static inline double ivmax(double al, double ah, double bl, double bh) { double t1 = fabs(ah - bl), t2 = fabs(bh - al); return t1 > t2 ? t1 : t2; }
static inline int owner(int d) { return d == 0 ? 1 : (d + 3) / 2; }

static void process(const Box *b, Acc *acc) {
    acc->visited++;
    double xl[KMAX], xh[KMAX], yl[KMAX], yh[KMAX];
    xl[0] = xh[0] = yl[0] = yh[0] = 0;
    xl[1] = b->lo[0]; xh[1] = b->hi[0]; yl[1] = yh[1] = 0;
    for (int j = 2; j < k; j++) { xl[j] = b->lo[2 * j - 3]; xh[j] = b->hi[2 * j - 3]; yl[j] = b->lo[2 * j - 2]; yh[j] = b->hi[2 * j - 2]; }
    /* symmetry order xi_2 <= xi_3 <= ... */
    int straddle = 0, sdim = -1, spair = -1; double swid = 0;
    for (int j = 2; j + 1 < k; j++) {
        if (xl[j] > xh[j + 1]) return;                       /* entirely out of order */
        if (xh[j] > xl[j + 1]) {
            straddle++; spair = j;
            double w1 = xh[j] - xl[j], w2 = xh[j + 1] - xl[j + 1];
            if (w1 > swid) { swid = w1; sdim = 2 * j - 3; }
            if (w2 > swid) { swid = w2; sdim = 2 * (j + 1) - 3; }
        }
    }
    long long pres = 0, und = 0; int involved = 0;
    double dmn[PMAX], dmx[PMAX];
    long long idx3 = 0;
    for (int p = 0; p < npairs; p++) {
        int i = pi_[p], j = pj_[p];
        double dxm = ivmin(xl[i], xh[i], xl[j], xh[j]), dym = ivmin(yl[i], yh[i], yl[j], yh[j]);
        double dxM = ivmax(xl[i], xh[i], xl[j], xh[j]), dyM = ivmax(yl[i], yh[i], yl[j], yh[j]);
        double dmin2 = dxm * dxm + dym * dym, dmax2 = dxM * dxM + dyM * dyM;
        dmn[p] = sqrt(dmin2); dmx[p] = sqrt(dmax2);
        if (dmax2 <= 1) { pres |= 1LL << p; idx3 += pow3[p]; }
        else if (dmin2 <= 1) { und |= 1LL << p; idx3 += 2 * pow3[p]; involved |= (1 << i) | (1 << j); }
    }
    int gmin = gmin3[idx3], gmax = gmax3[idx3];
    if (gmax <= 0) return;
    double width = 0, rwidth = 0; int dw = 0, drw = -1;
    for (int d = 0; d < m; d++) {
        double w = b->hi[d] - b->lo[d];
        if (w > width) { width = w; dw = d; }
        if (((involved >> owner(d)) & 1) && w > rwidth) { rwidth = w; drw = d; }
    }
    double v = 1; for (int d = 0; d < m; d++) v *= b->hi[d] - b->lo[d];
    int dsplit = -1;
    if (width > W0) { dsplit = dw; goto do_split; }
    {
        double xc[KMAX], yc[KMAX], del[KMAX], gx[KMAX], gy[KMAX], hw[DMAX];
        for (int i = 0; i < k; i++) { xc[i] = 0.5 * (xl[i] + xh[i]); yc[i] = 0.5 * (yl[i] + yh[i]); del[i] = 0.5 * hypot(xh[i] - xl[i], yh[i] - yl[i]); }
        for (int d = 0; d < m; d++) hw[d] = b->hi[d] - b->lo[d];
        double m1[KMAX], m2[KMAX], m4[KMAX];
        for (int i = 0; i < k; i++) {
            double a = 0.5 * (xh[i] - xl[i]), bb = 0.5 * (yh[i] - yl[i]);
            m2[i] = (a * a + bb * bb) / 3; m1[i] = sqrt(m2[i]);
            m4[i] = a * a * a * a / 5 + 2 * (a * a / 3) * (bb * bb / 3) + bb * bb * bb * bb / 5;
        }
        double Rmax = 0, Er = 0, sqrtEr2 = 0;
        int chk_nv[PMAX]; for (int p = 0; p < npairs; p++) chk_nv[p] = 0;   /* CHK */
        for (int p = 0; p < npairs && Rmax >= 0; p++) {
            if (dmn[p] >= 2) continue;
            if (dmn[p] <= 0) { Rmax = -1; break; }
            int i = pi_[p], j = pj_[p];
            double dd = dmx[p] < 2 ? dmx[p] : 2, dl = del[i] + del[j];
            /* vertex angular motion along a segment: radial part (TV of arcsin(d/2)) + tangential part (TV of the direction of
               y_j - y_i, = int |tau|/d <= min(|w|/d_min, pi)) */
            double cr, c0;
            if (dmx[p] < 1.98) { double hmin = 0.5 * sqrt(4 - dmx[p] * dmx[p]); cr = 1 / (2 * hmin); c0 = 0; }
            else { cr = 0; c0 = 2 * (asin(dd / 2) - asin(dmn[p] / 2)); }
            double tanmax = dl / dmn[p] < M_PI ? dl / dmn[p] : M_PI;
            double motion = cr * dl + c0 + tanmax;
            double ex = xc[j] - xc[i], ey = yc[j] - yc[i], dc = sqrt(ex * ex + ey * ey);
            int nv = 2;
            if (dc < 2 && dc > 0) {
                double hh = sqrt(1 - dc * dc / 4), ux = ex / dc, uy = ey / dc;
                nv = 0;
                for (int sgn = -1; sgn <= 1; sgn += 2) {
                    double px = xc[i] + 0.5 * dc * ux - sgn * hh * uy, py = yc[i] + 0.5 * dc * uy + sgn * hh * ux;
                    double pmove = del[i] + motion;
                    int cov = 0;
                    for (int q = 0; q < k && !cov; q++) {
                        if (q == i || q == j) continue;
                        double qx = px - xc[q], qy = py - yc[q];
                        if (sqrt(qx * qx + qy * qy) + pmove + del[q] < 1) cov = 1;
                    }
                    if (!cov) nv++;
                }
            }
            chk_nv[p] = nv;   /* CHK */
            if (!nv) continue;
            double S2 = m2[i] + m2[j] + 2 * m1[i] * m1[j], S1 = m1[i] + m1[j], S4 = 8 * (m4[i] + m4[j]);
            double d2 = dmn[p] * dmn[p];
            double Etan = S2 / dmn[p] < M_PI * S1 ? S2 / dmn[p] : M_PI * S1;
            double Etan2 = S4 / d2 < M_PI * M_PI * S2 ? S4 / d2 : M_PI * M_PI * S2;
            Rmax += nv * dl * motion;
            Er += nv * (cr * S2 + c0 * S1 + Etan);
            sqrtEr2 += nv * sqrt(3 * (cr * cr * S4 + c0 * c0 * S2 + Etan2));
        }
        if (Rmax < 0) {
            /* coincident centres possible (d_min = 0 for some pair): Lemma V does not apply; use the enlarged-radius bound
               A(y) <= area of the union of the disks B(c_i, 1 + delta), delta = max_i del_i (valid pointwise) */
            double delta = 0; for (int i = 0; i < k; i++) if (del[i] > delta) delta = del[i];
            double xs[KMAX], ys[KMAX], gx2[KMAX], gy2[KMAX];
            for (int i = 0; i < k; i++) { xs[i] = xc[i] / (1 + delta); ys[i] = yc[i] / (1 + delta); }
            double Aenl = (1 + delta) * (1 + delta) * union_area_grad(xs, ys, gx2, gy2);
            double Ac = union_area_grad(xc, yc, gx2, gy2);
            double c = (gmin > 0 && !straddle) ? v * 0.5 * gmin * b->lo[0] * pow(Aenl, -s_exp) : 0;
            double est = PREF * v * 0.5 * gmax * 0.5 * (b->lo[0] + b->hi[0]) * pow(Ac, -s_exp) - PREF * c;
            if (est > EPS && width > WF) { dsplit = dw; goto do_split; }
            acc->lb += c; acc->extra += c; acc->scored++; if (c == 0) { acc->voldrop += v; acc->dropped++; }
            { FInfo fi = { .flt = c, .enl = 1, .straddle = straddle, .spair = spair, .gmin = gmin, .gmax = gmax,   /* CHK */
                           .pres = pres, .und = und }; chk_leaf(b, &fi); }                                      /* CHK */
            acc->l_coi += est; return;
        }
        double A = union_area_grad(xc, yc, gx, gy);
        double bv[DMAX];
        bv[0] = gx[1];
        for (int j = 2; j < k; j++) { bv[2 * j - 3] = gx[j]; bv[2 * j - 2] = gy[j]; }
        double sumb = 0, sumb2 = 0;
        for (int d = 0; d < m; d++) { sumb += fabs(bv[d]) * hw[d] / 2; sumb2 += bv[d] * bv[d] * hw[d] * hw[d] / 12; }
        double ap = A + Er, tmin = A - sumb, r2c = 0.5 * (b->lo[0] + b->hi[0]);
        double val = 0;
        if (tmin > 0) {
            double t2 = sqrt(sumb2) + sqrtEr2;
            val = r2c * pow(ap, -s_exp) - s_exp * pow(A, -s_exp - 1) * (bv[0] * hw[0] * hw[0] / 12) - s_exp * pow(A, -s_exp - 1) * (hw[0] / 2) * Er
                  - (hw[0] / 4) * s_exp * (s_exp + 1) * pow(tmin, -s_exp - 2) * t2 * t2;
            if (val < 0) val = 0;
        }
        double mid = r2c * pow(A, -s_exp);
        double Alow = A - sumb - Rmax; if (Alow < M_PI) Alow = M_PI;
        double pot = PREF * v * 0.5 * gmax * b->hi[0] * pow(Alow, -s_exp);
        double fmin_pt = b->lo[0] * pow(A + sumb + Rmax, -s_exp);
        double fmax_pt = b->hi[0] * pow(Alow, -s_exp);          /* pointwise upper bound of r2 A^-s on the box */
        if (straddle) {
            double c = 0;
            if (straddle == 1 && gmin > 0) {
                int j = spair;
                double pord = cdf_diff(xl[j], xh[j], xl[j + 1], xh[j + 1], 0.0);
                double c1 = v * 0.5 * gmin * fmin_pt * pord;                         /* pointwise lower bound on the part */
                double c2 = v * 0.5 * gmin * (val - (1 - pord) * fmax_pt);           /* whole box minus the outside part */
                c = c1 > c2 ? c1 : c2;
            }
            double est = PREF * v * 0.5 * gmax * mid - PREF * c;          /* refinement estimate (not a bound) */
            if (est > EPS && swid > WF) { dsplit = sdim; goto do_split; }
            acc->lb += c; acc->extra += c; acc->scored++; if (c == 0) { acc->voldrop += v; acc->dropped++; }
            { FInfo fi = { .flt = c, .A = A, .Er = Er, .sqrtEr2 = sqrtEr2, .Rmax = Rmax, .val = val, .tmin = tmin,   /* CHK */
                           .straddle = straddle, .spair = spair, .gmin = gmin, .gmax = gmax, .pres = pres, .und = und }; /* CHK */
              memcpy(fi.nv, chk_nv, sizeof chk_nv); chk_leaf(b, &fi); }                                         /* CHK */
            acc->lossdrop += pot - PREF * c; acc->l_str += est;
            return;
        }
        double lbx = (gmin > 0) ? v * 0.5 * gmin * val : 0, extra = 0;
        if (gmin < gmax) {
            /* E g >= gmin + sum over joint states s of (one or two undetermined edges) of P_lo(s) (g_s - gmin), where g_s is
               the minimum of g over completions with those edges in state s; P_lo = product of the staircase bounds for two
               vertex-disjoint edges (independent), Frechet max(0, P1 + P2 - 1) otherwise */
            double best = 0, pin_[PMAX], pout_[PMAX]; int up[PMAX], nu = 0;
            #define EV(q) (((q) * fmin_pt) > (val - (1 - (q)) * fmax_pt) ? ((q) * fmin_pt) : (val - (1 - (q)) * fmax_pt))
            for (int p = 0; p < npairs; p++) {
                if (!((und >> p) & 1)) continue;
                int i = pi_[p], j = pj_[p];
                prob_unit(xl[i], xh[i], yl[i], yh[i], xl[j], xh[j], yl[j], yh[j], &pin_[nu], &pout_[nu]);
                up[nu++] = p;
                int gp = gmin3[idx3 - pow3[p]], ga = gmin3[idx3 - 2 * pow3[p]];
                double sc = (gp - gmin) * EV(pin_[nu - 1]) + (ga - gmin) * EV(pout_[nu - 1]);
                if (sc > best) best = sc;
            }
            for (int t1 = 0; t1 < nu; t1++) for (int t2 = t1 + 1; t2 < nu; t2++) {
                int p1 = up[t1], p2 = up[t2];
                int disjoint = pi_[p1] != pi_[p2] && pi_[p1] != pj_[p2] && pj_[p1] != pi_[p2] && pj_[p1] != pj_[p2];
                double sc = 0;
                for (int s1 = 0; s1 <= 1; s1++) for (int s2 = 0; s2 <= 1; s2++) {
                    long long id = idx3 - (s1 ? pow3[p1] : 2 * pow3[p1]) - (s2 ? pow3[p2] : 2 * pow3[p2]);
                    int gs = gmin3[id];
                    if (gs <= gmin) continue;
                    double q1 = s1 ? pin_[t1] : pout_[t1], q2 = s2 ? pin_[t2] : pout_[t2];
                    double pl = disjoint ? q1 * q2 : (q1 + q2 - 1 > 0 ? q1 + q2 - 1 : 0);
                    sc += EV(pl) * (gs - gmin);
                }
                if (sc > best) best = sc;
            }
            extra = v * 0.5 * best;
            double est = PREF * v * 0.5 * gmax * mid - PREF * (lbx + extra);   /* refinement estimate (not a bound) */
            if (est > EPS && rwidth > WF) { dsplit = drw; goto do_split; }
            acc->lossdrop += pot - PREF * (lbx + extra); acc->l_bnd += est;
        } else {
            double loss = PREF * v * 0.5 * gmin * (mid - val);
            if (loss > EPS && width > WF) { dsplit = dw; goto do_split; }
            acc->l_int += loss;
        }
        acc->lb += lbx + extra; acc->extra += extra;
        acc->mid += v * 0.5 * gmin * mid;
        acc->scored++;
        { FInfo fi = { .flt = lbx + extra, .A = A, .Er = Er, .sqrtEr2 = sqrtEr2, .Rmax = Rmax, .val = val, .tmin = tmin,   /* CHK */
                       .straddle = 0, .spair = -1, .gmin = gmin, .gmax = gmax, .pres = pres, .und = und };              /* CHK */
          memcpy(fi.nv, chk_nv, sizeof chk_nv); chk_leaf(b, &fi); }                                                     /* CHK */
        if (gmin <= 0) acc->dropped++;
        return;
    }
do_split:;
    double mid = 0.5 * (b->lo[dsplit] + b->hi[dsplit]);
    Box c = *b;
    c.hi[dsplit] = mid; process(&c, acc);
    c = *b; c.lo[dsplit] = mid; process(&c, acc);
}

/* split the root into at least n boxes (breadth first, widest coordinate) */
static Box *initial_boxes(const Box *root, int n, int *count) {
    int cap = 2 * n + 16, cnt = 1;
    Box *arr = malloc(sizeof(Box) * cap);
    arr[0] = *root;
    while (cnt < n) {
        Box *nb = malloc(sizeof(Box) * 2 * cnt); int nc = 0;
        for (int t = 0; t < cnt; t++) {
            int dw = 0; double w = -1;
            for (int d = 0; d < m; d++) if (arr[t].hi[d] - arr[t].lo[d] > w) { w = arr[t].hi[d] - arr[t].lo[d]; dw = d; }
            double mid = 0.5 * (arr[t].lo[dw] + arr[t].hi[dw]);
            nb[nc] = arr[t]; nb[nc].hi[dw] = mid; nc++;
            nb[nc] = arr[t]; nb[nc].lo[dw] = mid; nc++;
        }
        free(arr); arr = nb; cnt = nc;
    }
    *count = cnt;
    return arr;
}

/* ======================================================================================================================
 * Part B: rigorous leaf bounds in arb ball arithmetic.  Written from BOUNDS.md; the only inputs taken from Part A are the
 * dyadic box corners of each scored leaf (the FInfo values are used only for the comparison diagnostics).
 * ==================================================================================================================== */
#define RPREC 128
enum { R_CLASS, R_ZERO, R_TMIN, R_PRUNE, R_OTHER, NREASON };
static const char *reason_name[NREASON] = { "edge-class differs", "d^-=0 / coincident / undecidable", "tmin not certified > 0",
                                             "vertex pruning differs", "other" };
static int rnp, rpi[PMAX], rpj[PMAX];      /* own pair list (i < j, lexicographic; same order as box_ck8, for comparison) */
static signed char *g2own;                 /* own table: 2g(E) for every edge set E (bit p <-> pair p present) */
static double TPR;                         /* proxy circle length T' = (double) 2 pi */
static mag_t EPS_TPR;                      /* >= |2 pi - T'| */
static int mut_g = 0, mut_pref = 0, mut_orderfac = 0, mut_order = 0, mut_noR = 0, mut_class = 0, mut_old3b = 0, mut_flt = 0;
static int mut_indep = 0, mut_fmaxlo = 0;   /* controls for 3c/3d: treat all edge pairs as independent; fmax_pt := fmin_pt */
static int mut_enl1 = 0;                    /* control for 3e: no enlargement (R := 1, i.e. A_enl := A(c)) */
static int skip_zero_flt = 1, nstrip_log2 = 3;

typedef struct {
    arb_t sum_main, sum_tight;             /* sums of rigorous leaf lower bounds: BOUNDS.md 3b / tighter valid variant */
    double flt_sum, flt_eval;              /* float sum over all scored leaves / over the arb-evaluated ones */
    long long nleaf, nskip, nfast0, narb, nrig0, nclassdiff, nnvdiff, nbelow, nabove, nAdiff, ncentre_bad, nenl, nenl_diff;
    long long reason[NREASON];
    double reason_flt[NREASON], reason_rig[NREASON];
    double maxAdiff, maxEdiff, t_arb;
} RAcc;
static __thread RAcc *tl_racc;

/* ---------------- B1. own g table ---------------- */
static int own_next_perm(int *a, int n) {
    int i = n - 2; while (i >= 0 && a[i] >= a[i + 1]) i--;
    if (i < 0) return 0;
    int j = n - 1; while (a[j] <= a[i]) j--;
    int t = a[i]; a[i] = a[j]; a[j] = t;
    for (int l = i + 1, r = n - 1; l < r; l++, r--) { t = a[l]; a[l] = a[r]; a[r] = t; }
    return 1;
}
static void own_adj(long long E, int *adj) {
    for (int v = 0; v < k; v++) adj[v] = 0;
    for (int p = 0; p < rnp; p++) if ((E >> p) & 1) { adj[rpi[p]] |= 1 << rpj[p]; adj[rpj[p]] |= 1 << rpi[p]; }
}
static int own_connected(const int *adj) {
    int reach = 1, prev = 0;
    while (reach != prev) { prev = reach; for (int v = 0; v < k; v++) if ((reach >> v) & 1) reach |= adj[v]; }
    return reach == (1 << k) - 1;
}
/* 2g = 2p - n1 for connected graphs (p = minimum number of vertex-disjoint paths covering V, n1 = number of degree-1
   vertices), 0 for disconnected graphs.  p = 1 + min over all vertex orders of the number of consecutive pairs that are
   not adjacent (a cover by p paths concatenates to an order with <= p-1 such pairs; an order with b such pairs splits
   into b+1 paths). */
static int own_g2(long long E) {
    int adj[KMAX];
    own_adj(E, adj);
    if (!own_connected(adj)) return 0;
    int n1 = 0; for (int v = 0; v < k; v++) if (__builtin_popcount(adj[v]) == 1) n1++;
    int perm[KMAX], best = k;
    for (int v = 0; v < k; v++) perm[v] = v;
    do {
        int br = 0;
        for (int t = 0; t + 1 < k; t++) if (!((adj[perm[t]] >> perm[t + 1]) & 1)) { if (++br + 1 >= best) break; }
        if (br + 1 < best) best = br + 1;
    } while (best > 1 && own_next_perm(perm, k));
    return 2 * best - n1;
}
static void own_build_g(void) {
    rnp = 0;
    for (int i = 0; i < k; i++) for (int j = i + 1; j < k; j++) { rpi[rnp] = i; rpj[rnp] = j; rnp++; }
    long long ng = 1LL << rnp;
    g2own = malloc(ng);
    #pragma omp parallel for schedule(dynamic, 256)
    for (long long E = 0; E < ng; E++) g2own[E] = (signed char)own_g2(E);
    if (mut_g) {                         /* negative control: 2g += 1 on every connected graph (gmin increased) */
        for (long long E = 0; E < ng; E++) { int adj[KMAX]; own_adj(E, adj); if (own_connected(adj)) g2own[E] += 1; }
    }
}
/* state[p]: 0 absent, 1 present, 2 undetermined.  gmin/gmax over all completions; gpres[p] / gabs[p] = min of 2g over the
   completions with p present / absent (undetermined p only). */
static void own_g_bounds(const int *state, int *gmin, int *gmax, int *gpres, int *gabs) {
    long long base = 0; int ul[PMAX], nu = 0;
    for (int p = 0; p < rnp; p++) { gpres[p] = gabs[p] = 1000; if (state[p] == 1) base |= 1LL << p; else if (state[p] == 2) ul[nu++] = p; }
    int mn = 1000, mx = -1000;
    for (long long c = 0; c < (1LL << nu); c++) {
        long long E = base;
        for (int t = 0; t < nu; t++) if ((c >> t) & 1) E |= 1LL << ul[t];
        int g = g2own[E];
        if (g < mn) mn = g;
        if (g > mx) mx = g;
        for (int t = 0; t < nu; t++) {
            int p = ul[t];
            if ((c >> t) & 1) { if (g < gpres[p]) gpres[p] = g; } else { if (g < gabs[p]) gabs[p] = g; }
        }
    }
    *gmin = mn; *gmax = mx;
}

/* pair version: for the list ul[0..nu) of undetermined pairs, g2pair[(t1 * PMAX + t2) * 4 + 2 s1 + s2] (t1 < t2) = min of 2g over
   the completions with ul[t1] in state s1 and ul[t2] in state s2 (1 = present); single-edge minima as in own_g_bounds. */
static void own_g_bounds2(const int *state, int *gmin, int *gmax, int *gpres, int *gabs, int *ul, int *nu_out, int *g2pair) {
    long long base = 0; int nu = 0;
    for (int p = 0; p < rnp; p++) { gpres[p] = gabs[p] = 1000; if (state[p] == 1) base |= 1LL << p; else if (state[p] == 2) ul[nu++] = p; }
    for (int t1 = 0; t1 < nu; t1++) for (int t2 = t1 + 1; t2 < nu; t2++) for (int s = 0; s < 4; s++) g2pair[(t1 * PMAX + t2) * 4 + s] = 1000;
    int mn = 1000, mx = -1000;
    for (long long c = 0; c < (1LL << nu); c++) {
        long long E = base;
        for (int t = 0; t < nu; t++) if ((c >> t) & 1) E |= 1LL << ul[t];
        int g = g2own[E];
        if (g < mn) mn = g;
        if (g > mx) mx = g;
        for (int t = 0; t < nu; t++) {
            int p = ul[t];
            if ((c >> t) & 1) { if (g < gpres[p]) gpres[p] = g; } else { if (g < gabs[p]) gabs[p] = g; }
        }
        for (int t1 = 0; t1 < nu; t1++) for (int t2 = t1 + 1; t2 < nu; t2++) {
            int *q = &g2pair[(t1 * PMAX + t2) * 4 + 2 * (int)((c >> t1) & 1) + (int)((c >> t2) & 1)];
            if (g < *q) *q = g;
        }
    }
    *gmin = mn; *gmax = mx; *nu_out = nu;
}

/* ---------------- B2. exact dyadic helpers ---------------- */
static void arf_dsub(arf_t z, double x, double y) {           /* z = x - y exactly */
    arf_t t; arf_init(t); arf_set_d(z, x); arf_set_d(t, y); arf_sub(z, z, t, ARF_PREC_EXACT, ARF_RND_DOWN); arf_clear(t);
}
/* gap = min |x - y|, span = max |x - y| over x in [al, ah], y in [bl, bh] (exact) */
static void exact_gap_span(arf_t gap, arf_t span, double al, double ah, double bl, double bh) {
    arf_t t1, t2; arf_init(t1); arf_init(t2);
    arf_dsub(t1, bl, ah); arf_dsub(t2, al, bh);
    arf_zero(gap);
    if (arf_cmp(t1, gap) > 0) arf_set(gap, t1);
    if (arf_cmp(t2, gap) > 0) arf_set(gap, t2);
    arf_abs(t1, t1); arf_abs(t2, t2);
    arf_set(span, arf_cmp(t1, t2) >= 0 ? t1 : t2);
    arf_clear(t1); arf_clear(t2);
}
static void exact_d2(arf_t d2min, arf_t d2max, int i, int j, const double *xl, const double *xh, const double *yl, const double *yh) {
    arf_t gx, sx, gy, sy, t; arf_init(gx); arf_init(sx); arf_init(gy); arf_init(sy); arf_init(t);
    exact_gap_span(gx, sx, xl[i], xh[i], xl[j], xh[j]);
    exact_gap_span(gy, sy, yl[i], yh[i], yl[j], yh[j]);
    arf_mul(d2min, gx, gx, ARF_PREC_EXACT, ARF_RND_DOWN); arf_mul(t, gy, gy, ARF_PREC_EXACT, ARF_RND_DOWN);
    arf_add(d2min, d2min, t, ARF_PREC_EXACT, ARF_RND_DOWN);
    arf_mul(d2max, sx, sx, ARF_PREC_EXACT, ARF_RND_DOWN); arf_mul(t, sy, sy, ARF_PREC_EXACT, ARF_RND_DOWN);
    arf_add(d2max, d2max, t, ARF_PREC_EXACT, ARF_RND_DOWN);
    arf_clear(gx); arf_clear(sx); arf_clear(gy); arf_clear(sy); arf_clear(t);
}

/* ---------------- B3. union area and gradient at the box centre ---------------- */
/* Circle i, disk j at distance d in (0, 2): disk j covers exactly the closed arc |t - phi| <= alpha of circle i
   (phi = direction of y_j - y_i, alpha = acos(d/2)).  The exposed set E_i is the complement of these arcs and
     A = sum_i int_{E_i} (1 + x_i cos t + y_i sin t)/2 dt,     grad_{y_i} A = int_{E_i} (cos t, sin t) dt.
   We replace every true endpoint (an arb ball) by an exact double proxy and the circle R/2piZ by the proxy circle
   R/T'Z; the proxy exposed set E'' is then computed exactly (comparisons of doubles; h - T' is exact by Sterbenz) and
   int_{E''} is evaluated in arb.  With rho_L, rho_H >= |true endpoint - proxy| (same lift) and eps >= |2 pi - T'|,
     meas(E_i symdiff E''_i) <= M_i = eps (1 + 4 n_i) + 3 sum_j (rho_L,j + rho_H,j)        (n_i = number of arcs)
   (each arc: lifts m = -1, 0, 1 each contribute <= rho_L + rho_H + 2|m| eps; plus [0,2pi) symdiff [0,T')), so the area
   term changes by at most M_i (1 + |x_i| + |y_i|)/2 and each gradient component by at most M_i.
   Returns 0, or -1 if two centres coincide (or a distance comparison is undecidable). */
static void add_arc(arb_t Ai, arb_t gxi, arb_t gyi, double a, double b, double x, double y, slong prec) {
    arb_t t, sa, ca, sb, cb, u;
    arb_init(t); arb_init(sa); arb_init(ca); arb_init(sb); arb_init(cb); arb_init(u);
    arb_set_d(t, a); arb_sin_cos(sa, ca, t, prec);
    arb_set_d(u, b); arb_sin_cos(sb, cb, u, prec);
    arb_sub(u, u, t, prec);                                   /* b - a */
    arb_sub(t, sb, sa, prec); arb_add(gxi, gxi, t, prec);     /* sin b - sin a */
    arb_set_d(sa, x); arb_mul(t, t, sa, prec); arb_add(u, u, t, prec);
    arb_sub(t, ca, cb, prec); arb_add(gyi, gyi, t, prec);     /* cos a - cos b */
    arb_set_d(sa, y); arb_mul(t, t, sa, prec); arb_add(u, u, t, prec);   /* (b-a) + x (sin b - sin a) - y (cos b - cos a) */
    arb_mul_2exp_si(u, u, -1);
    arb_add(Ai, Ai, u, prec);
    arb_clear(t); arb_clear(sa); arb_clear(ca); arb_clear(sb); arb_clear(cb); arb_clear(u);
}
static void abs_ub_mag(mag_t out, const arb_t x) {          /* out >= |x| for every point of the ball */
    arf_t u; arf_init(u); arb_get_abs_ubound_arf(u, x, 53); arf_get_mag(out, u); arf_clear(u);
}
static int rig_union(arb_t A, arb_ptr gx, arb_ptr gy, const double *xc, const double *yc, slong prec) {
    int ret = 0, has[PMAX];
    arb_t pi, twopi, t, u, d2, dd, Ai, cang, L, H;
    arb_t phi[PMAX], alp[PMAX];
    arb_init(pi); arb_init(twopi); arb_init(t); arb_init(u); arb_init(d2); arb_init(dd); arb_init(Ai); arb_init(cang);
    arb_init(L); arb_init(H);
    for (int p = 0; p < rnp; p++) { arb_init(phi[p]); arb_init(alp[p]); }
    mag_t M, rho, tm, supf;
    mag_init(M); mag_init(rho); mag_init(tm); mag_init(supf);
    arb_const_pi(pi, prec); arb_mul_2exp_si(twopi, pi, 1);
    for (int p = 0; p < rnp; p++) {
        has[p] = 0;
        int i = rpi[p], j = rpj[p];
        arb_set_d(t, xc[j]); arb_set_d(dd, xc[i]); arb_sub(t, t, dd, prec);     /* dx */
        arb_set_d(u, yc[j]); arb_set_d(dd, yc[i]); arb_sub(u, u, dd, prec);     /* dy */
        arb_sqr(d2, t, prec); arb_sqr(dd, u, prec); arb_add(d2, d2, dd, prec);
        if (arb_contains_zero(d2)) { ret = -1; goto done; }
        arb_set_ui(dd, 4);
        if (arb_ge(d2, dd)) continue;                 /* d >= 2: disk j meets circle i in at most one point */
        if (!arb_lt(d2, dd)) { ret = -1; goto done; }
        has[p] = 1;
        arb_atan2(phi[p], u, t, prec);
        arb_sqrt(dd, d2, prec); arb_mul_2exp_si(dd, dd, -1); arb_acos(alp[p], dd, prec);
    }
    arb_zero(A);
    for (int i = 0; i < k; i++) {
        arb_zero(gx + i); arb_zero(gy + i);
        double ivs[2 * KMAX], ive[2 * KMAX]; int niv = 0, narc = 0;
        mag_zero(rho);
        for (int p = 0; p < rnp; p++) {
            if (!has[p] || (rpi[p] != i && rpj[p] != i)) continue;
            narc++;
            arb_set(cang, phi[p]);
            if (rpj[p] == i) arb_add(cang, cang, pi, prec);            /* direction from y_i to the other centre */
            arb_sub(L, cang, alp[p], prec); arb_add(H, cang, alp[p], prec);
            double lm = arf_get_d(arb_midref(L), ARF_RND_NEAR);
            int nl = 0;
            while (lm + nl * TPR < 0) nl++;
            while (lm + nl * TPR >= TPR) nl--;
            if (nl) { arb_mul_si(t, twopi, nl, prec); arb_add(L, L, t, prec); arb_add(H, H, t, prec); }
            double l2 = arf_get_d(arb_midref(L), ARF_RND_NEAR), h2 = arf_get_d(arb_midref(H), ARF_RND_NEAR);
            if (!isfinite(l2) || !isfinite(h2) || !arb_is_finite(L) || !arb_is_finite(H)) { ret = -1; goto done; }
            if (l2 < 0) l2 = 0;
            if (l2 >= TPR) l2 = nextafter(TPR, 0);
            if (h2 < l2) h2 = l2;
            if (!(h2 <= 2 * TPR)) { ret = -1; goto done; }
            arb_set_d(t, l2); arb_sub(t, L, t, prec); abs_ub_mag(tm, t); mag_add(rho, rho, tm);
            arb_set_d(t, h2); arb_sub(t, H, t, prec); abs_ub_mag(tm, t); mag_add(rho, rho, tm);
            if (h2 <= TPR) { ivs[niv] = l2; ive[niv] = h2; niv++; }
            else { ivs[niv] = l2; ive[niv] = TPR; niv++; ivs[niv] = 0; ive[niv] = h2 - TPR; niv++; }
        }
        if (narc == 0) { arb_add(A, A, pi, prec); continue; }   /* whole circle exposed: pi, gradient 0 (exact) */
        mag_mul_ui(M, EPS_TPR, 1 + 4 * narc); mag_mul_ui(tm, rho, 3); mag_add(M, M, tm);
        for (int s = 1; s < niv; s++) {                       /* insertion sort by start */
            double a0 = ivs[s], b0 = ive[s]; int r = s - 1;
            while (r >= 0 && ivs[r] > a0) { ivs[r + 1] = ivs[r]; ive[r + 1] = ive[r]; r--; }
            ivs[r + 1] = a0; ive[r + 1] = b0;
        }
        arb_zero(Ai);
        double cur = 0;
        for (int s = 0; s < niv; s++) {
            if (ivs[s] > cur) add_arc(Ai, gx + i, gy + i, cur, ivs[s], xc[i], yc[i], prec);
            if (ive[s] > cur) cur = ive[s];
        }
        if (cur < TPR) add_arc(Ai, gx + i, gy + i, cur, TPR, xc[i], yc[i], prec);
        /* error terms: sup |(1 + x cos + y sin)/2| <= (1 + |x| + |y|)/2, sup |cos|, |sin| <= 1 */
        mag_set_d(supf, fabs(xc[i])); mag_set_d(tm, fabs(yc[i])); mag_add(supf, supf, tm);
        mag_one(tm); mag_add(supf, supf, tm); mag_mul_2exp_si(supf, supf, -1);
        mag_mul(tm, M, supf); arb_add_error_mag(Ai, tm);
        arb_add_error_mag(gx + i, M); arb_add_error_mag(gy + i, M);
        arb_add(A, A, Ai, prec);
    }
done:
    arb_clear(pi); arb_clear(twopi); arb_clear(t); arb_clear(u); arb_clear(d2); arb_clear(dd); arb_clear(Ai); arb_clear(cang);
    arb_clear(L); arb_clear(H);
    for (int p = 0; p < rnp; p++) { arb_clear(phi[p]); arb_clear(alp[p]); }
    mag_clear(M); mag_clear(rho); mag_clear(tm); mag_clear(supf);
    return ret;
}

/* ---------------- B3e. union area of enlarged disks (BOUNDS.md 3e) ---------------- */
/* Area of the union of the closed disks B(c_i, R), exact dyadic centres (identical centres merged: the union of equal disks
   is one disk), exact radius R > 0 (arf).  Disk j covers the closed arc |t - phi| <= acos(d/(2R)) of circle i, and
   A = sum_i int_{E_i} (R^2 + R x_i cos t + R y_i sin t)/2 dt; same exact-proxy / proxy-circle method and symmetric-difference
   error term as rig_union (sup of the integrand <= (R^2 + R (|x| + |y|))/2).  Returns 0, or -1 if a tangency is undecidable. */
static void add_arc_R(arb_t Ai, double a, double b, double x, double y, const arb_t R, slong prec) {
    arb_t t, sa, ca, sb, cb, u, w;
    arb_init(t); arb_init(sa); arb_init(ca); arb_init(sb); arb_init(cb); arb_init(u); arb_init(w);
    arb_set_d(t, a); arb_sin_cos(sa, ca, t, prec);
    arb_set_d(u, b); arb_sin_cos(sb, cb, u, prec);
    arb_sub(u, u, t, prec); arb_mul(u, u, R, prec);            /* R (b - a) */
    arb_sub(t, sb, sa, prec); arb_set_d(w, x); arb_mul(t, t, w, prec); arb_add(u, u, t, prec);
    arb_sub(t, ca, cb, prec); arb_set_d(w, y); arb_mul(t, t, w, prec); arb_add(u, u, t, prec);
    arb_mul(u, u, R, prec); arb_mul_2exp_si(u, u, -1);         /* (R^2 (b-a) + R x (sin b - sin a) - R y (cos b - cos a))/2 */
    arb_add(Ai, Ai, u, prec);
    arb_clear(t); arb_clear(sa); arb_clear(ca); arb_clear(sb); arb_clear(cb); arb_clear(u); arb_clear(w);
}
static int rig_union_R(arb_t A, const double *xc, const double *yc, const arf_t Rex, slong prec) {
    int ret = 0, has[PMAX], dup[KMAX];
    arb_t R, fourR2, pi, twopi, t, u, d2, dd, Ai, cang, L, H;
    arb_t phi[PMAX], alp[PMAX];
    arb_init(R); arb_init(fourR2); arb_init(pi); arb_init(twopi); arb_init(t); arb_init(u); arb_init(d2); arb_init(dd);
    arb_init(Ai); arb_init(cang); arb_init(L); arb_init(H);
    for (int p = 0; p < rnp; p++) { arb_init(phi[p]); arb_init(alp[p]); }
    mag_t M, rho, tm, supf;
    mag_init(M); mag_init(rho); mag_init(tm); mag_init(supf);
    arb_set_arf(R, Rex); arb_sqr(fourR2, R, prec); arb_mul_2exp_si(fourR2, fourR2, 2);
    arb_const_pi(pi, prec); arb_mul_2exp_si(twopi, pi, 1);
    for (int i = 0; i < k; i++) { dup[i] = 0; for (int j = 0; j < i; j++) if (!dup[j] && xc[j] == xc[i] && yc[j] == yc[i]) dup[i] = 1; }
    for (int p = 0; p < rnp; p++) {
        has[p] = 0;
        int i = rpi[p], j = rpj[p];
        if (dup[i] || dup[j]) continue;
        arb_set_d(t, xc[j]); arb_set_d(dd, xc[i]); arb_sub(t, t, dd, prec);
        arb_set_d(u, yc[j]); arb_set_d(dd, yc[i]); arb_sub(u, u, dd, prec);
        arb_sqr(d2, t, prec); arb_sqr(dd, u, prec); arb_add(d2, d2, dd, prec);
        if (arb_contains_zero(d2)) { ret = -1; goto done; }             /* not reached: identical centres were merged */
        if (arb_ge(d2, fourR2)) continue;                              /* d >= 2R: at most a tangent point */
        if (!arb_lt(d2, fourR2)) { ret = -1; goto done; }
        has[p] = 1;
        arb_atan2(phi[p], u, t, prec);
        arb_sqrt(dd, d2, prec); arb_div(dd, dd, R, prec); arb_mul_2exp_si(dd, dd, -1); arb_acos(alp[p], dd, prec);
    }
    arb_zero(A);
    for (int i = 0; i < k; i++) {
        if (dup[i]) continue;
        double ivs[2 * KMAX], ive[2 * KMAX]; int niv = 0, narc = 0;
        mag_zero(rho);
        for (int p = 0; p < rnp; p++) {
            if (!has[p] || (rpi[p] != i && rpj[p] != i)) continue;
            narc++;
            arb_set(cang, phi[p]);
            if (rpj[p] == i) arb_add(cang, cang, pi, prec);
            arb_sub(L, cang, alp[p], prec); arb_add(H, cang, alp[p], prec);
            double lm = arf_get_d(arb_midref(L), ARF_RND_NEAR);
            int nl = 0;
            while (lm + nl * TPR < 0) nl++;
            while (lm + nl * TPR >= TPR) nl--;
            if (nl) { arb_mul_si(t, twopi, nl, prec); arb_add(L, L, t, prec); arb_add(H, H, t, prec); }
            double l2 = arf_get_d(arb_midref(L), ARF_RND_NEAR), h2 = arf_get_d(arb_midref(H), ARF_RND_NEAR);
            if (!isfinite(l2) || !isfinite(h2) || !arb_is_finite(L) || !arb_is_finite(H)) { ret = -1; goto done; }
            if (l2 < 0) l2 = 0;
            if (l2 >= TPR) l2 = nextafter(TPR, 0);
            if (h2 < l2) h2 = l2;
            if (!(h2 <= 2 * TPR)) { ret = -1; goto done; }
            arb_set_d(t, l2); arb_sub(t, L, t, prec); abs_ub_mag(tm, t); mag_add(rho, rho, tm);
            arb_set_d(t, h2); arb_sub(t, H, t, prec); abs_ub_mag(tm, t); mag_add(rho, rho, tm);
            if (h2 <= TPR) { ivs[niv] = l2; ive[niv] = h2; niv++; }
            else { ivs[niv] = l2; ive[niv] = TPR; niv++; ivs[niv] = 0; ive[niv] = h2 - TPR; niv++; }
        }
        if (narc == 0) { arb_sqr(t, R, prec); arb_mul(t, t, pi, prec); arb_add(A, A, t, prec); continue; }   /* pi R^2 */
        mag_mul_ui(M, EPS_TPR, 1 + 4 * narc); mag_mul_ui(tm, rho, 3); mag_add(M, M, tm);
        for (int s = 1; s < niv; s++) {
            double a0 = ivs[s], b0 = ive[s]; int r = s - 1;
            while (r >= 0 && ivs[r] > a0) { ivs[r + 1] = ivs[r]; ive[r + 1] = ive[r]; r--; }
            ivs[r + 1] = a0; ive[r + 1] = b0;
        }
        arb_zero(Ai);
        double cur = 0;
        for (int s = 0; s < niv; s++) {
            if (ivs[s] > cur) add_arc_R(Ai, cur, ivs[s], xc[i], yc[i], R, prec);
            if (ive[s] > cur) cur = ive[s];
        }
        if (cur < TPR) add_arc_R(Ai, cur, TPR, xc[i], yc[i], R, prec);
        /* sup |integrand| <= (R^2 + R (|x| + |y|))/2 */
        abs_ub_mag(supf, R); mag_set_d(tm, fabs(xc[i])); { mag_t t2; mag_init(t2); mag_set_d(t2, fabs(yc[i])); mag_add(tm, tm, t2); mag_add(tm, tm, supf); mag_clear(t2); }
        mag_mul(supf, supf, tm); mag_mul_2exp_si(supf, supf, -1);
        mag_mul(tm, M, supf); arb_add_error_mag(Ai, tm);
        arb_add(A, A, Ai, prec);
    }
done:
    arb_clear(R); arb_clear(fourR2); arb_clear(pi); arb_clear(twopi); arb_clear(t); arb_clear(u); arb_clear(d2); arb_clear(dd);
    arb_clear(Ai); arb_clear(cang); arb_clear(L); arb_clear(H);
    for (int p = 0; p < rnp; p++) { arb_clear(phi[p]); arb_clear(alp[p]); }
    mag_clear(M); mag_clear(rho); mag_clear(tm); mag_clear(supf);
    return ret;
}

/* ---------------- B4. Lemma V remainder (BOUNDS.md 3a, box_ck14 version with the tangential cap) ---------------- */
/* Outputs Rmax >= max_Q r, Er >= E r, sEr2 >= sqrt(E r^2) (uniform measure on Q), with
     r(delta) = sum_{pairs, unpruned vertices} (|delta_i| + |delta_j|) (c_r |delta_j - delta_i| + c0 + min(|delta_j - delta_i|/d^-, pi)),
   and the unpruned vertex counts nv[p].  Bounds: |delta_j - delta_i| <= u := |delta_i| + |delta_j|, u <= del_i + del_j;
   E u <= m1_i + m1_j, E u^2 <= m2_i + m2_j + 2 m1_i m1_j (independent points), E u^4 <= 8 (m4_i + m4_j);
   r_P^2 <= (c1 u^2 + c0 u)^2 <= 2 c1^2 u^4 + 2 c0^2 u^2; Minkowski over vertices.
   Returns -1 if some pair with d^- < 2 has d^- = 0 (no bound available). */
static int rig_remainder(arb_t Rmax, arb_t Er, arb_t sEr2, int *nv, const double *xl, const double *xh, const double *yl,
                         const double *yh, const double *xc, const double *yc, arb_srcptr d2mn, arb_srcptr d2mx, slong prec) {
    int ret = 0;
    arb_t del[KMAX], m1[KMAX], m2[KMAX], m4[KMAX];
    arb_t a, bb, a2, b2, t, u, w, four, one, dmn, dmx, c0, c1, dl, motion, hh, ex, ey, dc, px, py, S1, S2, S4, pi, tcap, Et, Et2;
    for (int i = 0; i < k; i++) { arb_init(del[i]); arb_init(m1[i]); arb_init(m2[i]); arb_init(m4[i]); }
    arb_init(a); arb_init(bb); arb_init(a2); arb_init(b2); arb_init(t); arb_init(u); arb_init(w); arb_init(four); arb_init(one);
    arb_init(dmn); arb_init(dmx); arb_init(c0); arb_init(c1); arb_init(dl); arb_init(motion); arb_init(hh); arb_init(ex);
    arb_init(ey); arb_init(dc); arb_init(px); arb_init(py); arb_init(S1); arb_init(S2); arb_init(S4); arb_init(pi);
    arb_init(tcap); arb_init(Et); arb_init(Et2);
    arb_set_ui(four, 4); arb_one(one); arb_const_pi(pi, prec);
    arb_zero(Rmax); arb_zero(Er); arb_zero(sEr2);
    for (int p = 0; p < rnp; p++) nv[p] = 0;
    for (int i = 0; i < k; i++) {                    /* point i uniform on a rectangle with half-sides (a, bb) */
        arb_set_d(a, xh[i]); arb_set_d(t, xl[i]); arb_sub(a, a, t, prec); arb_mul_2exp_si(a, a, -1);
        arb_set_d(bb, yh[i]); arb_set_d(t, yl[i]); arb_sub(bb, bb, t, prec); arb_mul_2exp_si(bb, bb, -1);
        arb_sqr(a2, a, prec); arb_sqr(b2, bb, prec);
        arb_add(t, a2, b2, prec); arb_sqrt(del[i], t, prec);          /* half diagonal */
        arb_div_ui(m2[i], t, 3, prec); arb_sqrt(m1[i], m2[i], prec);  /* E|d|^2 = (a^2+b^2)/3, E|d| <= sqrt */
        arb_sqr(t, a2, prec); arb_div_ui(t, t, 5, prec);              /* E|d|^4 = a^4/5 + 2 a^2 b^2/9 + b^4/5 */
        arb_mul(u, a2, b2, prec); arb_mul_2exp_si(u, u, 1); arb_div_ui(u, u, 9, prec); arb_add(t, t, u, prec);
        arb_sqr(u, b2, prec); arb_div_ui(u, u, 5, prec); arb_add(m4[i], t, u, prec);
    }
    if (mut_noR) goto done;                           /* negative control: pretend r = 0 */
    for (int p = 0; p < rnp; p++) {
        int i = rpi[p], j = rpj[p];
        if (arb_ge(d2mn + p, four)) continue;         /* d^- >= 2: no intersection vertex anywhere in Q */
        if (arb_contains_zero(d2mn + p)) { ret = -1; goto done; }
        arb_sqrt(dmn, d2mn + p, prec); arb_sqrt(dmx, d2mx + p, prec);
        arb_add(dl, del[i], del[j], prec);
        double dmaxd = sqrt(arf_get_d(arb_midref(d2mx + p), ARF_RND_NEAR));
        /* radial part: c1 (= c_r of BOUNDS.md) |w| + c0; tangential part (TV of the direction of y_j - y_i along a segment
           not through 0): <= min(|w|/d^-, pi) */
        if (dmaxd < 1.98 && arb_lt(d2mx + p, four)) {
            /* d stays <= d^+ < 2: c_r = 1/(2 h_min), c0 = 0, h_min = sqrt(4 - d^+^2)/2 */
            arb_sub(t, four, d2mx + p, prec); arb_sqrt(t, t, prec);  /* 2 h_min */
            arb_inv(c1, t, prec);
            arb_zero(c0);
        } else {
            /* c_r = 0, c0 = 2 (asin(min(d^+,2)/2) - asin(d^-/2)) (upper bound if a ball touches 1) */
            arb_zero(c1);
            arb_mul_2exp_si(t, dmx, -1);
            if (arb_lt(d2mx + p, four) && arb_lt(t, one)) arb_asin(u, t, prec); else arb_mul_2exp_si(u, pi, -1);
            arb_mul_2exp_si(t, dmn, -1);
            if (arb_lt(t, one)) arb_asin(w, t, prec); else arb_zero(w);
            arb_sub(c0, u, w, prec); arb_mul_2exp_si(c0, c0, 1);
        }
        arb_div(tcap, dl, dmn, prec); arb_min(tcap, tcap, pi, prec);         /* min(dl/d^-, pi) */
        arb_mul(motion, c1, dl, prec); arb_add(motion, motion, c0, prec); arb_add(motion, motion, tcap, prec);   /* max angular motion */
        /* vertex pruning: vertex P of the pair at the centre c (needs 0 < |c_j - c_i| < 2); P stays inside disk q on
           all of Q if |P(c) - c_q| + (del_i + motion) + del_q < 1 certainly */
        arb_set_d(ex, xc[j]); arb_set_d(t, xc[i]); arb_sub(ex, ex, t, prec);
        arb_set_d(ey, yc[j]); arb_set_d(t, yc[i]); arb_sub(ey, ey, t, prec);
        arb_sqr(t, ex, prec); arb_sqr(u, ey, prec); arb_add(w, t, u, prec);  /* |c_j - c_i|^2 */
        int nvp = 2;
        if (arb_is_positive(w) && arb_lt(w, four)) {
            arb_sqrt(dc, w, prec);
            arb_mul_2exp_si(t, w, -2); arb_sub(t, one, t, prec); arb_sqrt(hh, t, prec);  /* sqrt(1 - dc^2/4) */
            arb_div(hh, hh, dc, prec);                                                    /* h / dc */
            nvp = 0;
            for (int sg = -1; sg <= 1; sg += 2) {
                /* P = c_i + (c_j - c_i)/2 + sg (h/dc) (-(ey), ex) */
                arb_mul(t, hh, ey, prec); arb_mul_si(t, t, -sg, prec);
                arb_mul_2exp_si(px, ex, -1); arb_add(px, px, t, prec); arb_set_d(t, xc[i]); arb_add(px, px, t, prec);
                arb_mul(t, hh, ex, prec); arb_mul_si(t, t, sg, prec);
                arb_mul_2exp_si(py, ey, -1); arb_add(py, py, t, prec); arb_set_d(t, yc[i]); arb_add(py, py, t, prec);
                int cov = 0;
                for (int q = 0; q < k && !cov; q++) {
                    if (q == i || q == j) continue;
                    arb_set_d(t, xc[q]); arb_sub(t, px, t, prec); arb_sqr(t, t, prec);
                    arb_set_d(u, yc[q]); arb_sub(u, py, u, prec); arb_sqr(u, u, prec);
                    arb_add(t, t, u, prec); arb_sqrt(t, t, prec);
                    arb_add(t, t, del[i], prec); arb_add(t, t, motion, prec); arb_add(t, t, del[q], prec);
                    if (arb_lt(t, one)) cov = 1;
                }
                if (!cov) nvp++;
            }
        }
        nv[p] = nvp;
        if (!nvp) continue;
        arb_add(S1, m1[i], m1[j], prec);
        arb_mul(S2, m1[i], m1[j], prec); arb_mul_2exp_si(S2, S2, 1); arb_add(S2, S2, m2[i], prec); arb_add(S2, S2, m2[j], prec);
        arb_add(S4, m4[i], m4[j], prec); arb_mul_2exp_si(S4, S4, 3);
        /* r_v <= X (c_r X + c0 + min(X/d^-, pi)), X = |d_i| + |d_j| <= dl:
           E r_v <= c_r E X^2 + c0 E X + min(E X^2/d^-, pi E X),
           E r_v^2 <= 3 (c_r^2 E X^4 + c0^2 E X^2 + min(E X^4/d^-^2, pi^2 E X^2)) */
        arb_div(Et, S2, dmn, prec); arb_mul(t, pi, S1, prec); arb_min(Et, Et, t, prec);
        arb_div(Et2, S4, d2mn + p, prec); arb_sqr(t, pi, prec); arb_mul(t, t, S2, prec); arb_min(Et2, Et2, t, prec);
        arb_mul(t, dl, motion, prec); arb_mul_ui(t, t, nvp, prec); arb_add(Rmax, Rmax, t, prec);
        arb_mul(t, c1, S2, prec); arb_mul(u, c0, S1, prec); arb_add(t, t, u, prec); arb_add(t, t, Et, prec);
        arb_mul_ui(t, t, nvp, prec); arb_add(Er, Er, t, prec);
        arb_sqr(t, c1, prec); arb_mul(t, t, S4, prec); arb_sqr(u, c0, prec); arb_mul(u, u, S2, prec); arb_add(t, t, u, prec);
        arb_add(t, t, Et2, prec); arb_mul_ui(t, t, 3, prec); arb_sqrt(t, t, prec); arb_mul_ui(t, t, nvp, prec);
        arb_add(sEr2, sEr2, t, prec);
    }
done:
    for (int i = 0; i < k; i++) { arb_clear(del[i]); arb_clear(m1[i]); arb_clear(m2[i]); arb_clear(m4[i]); }
    arb_clear(a); arb_clear(bb); arb_clear(a2); arb_clear(b2); arb_clear(t); arb_clear(u); arb_clear(w); arb_clear(four);
    arb_clear(one); arb_clear(dmn); arb_clear(dmx); arb_clear(c0); arb_clear(c1); arb_clear(dl); arb_clear(motion);
    arb_clear(hh); arb_clear(ex); arb_clear(ey); arb_clear(dc); arb_clear(px); arb_clear(py); arb_clear(S1); arb_clear(S2);
    arb_clear(S4); arb_clear(pi); arb_clear(tcap); arb_clear(Et); arb_clear(Et2);
    return ret;
}

/* ---------------- B5. probabilities ---------------- */
/* ball containing F(z) = P(X - Y <= z), X ~ U[a,b], Y ~ U[c,d] independent (exact doubles; degenerate intervals allowed),
   z exact.  Closed form: with w1 = b-a, w2 = d-c > 0, p = min, q = max, u = z - (a - d):
     F = 0 (u <= 0), u^2/(2pq) (u <= p), (2u - p)/(2q) (u <= q), 1 - (p+q-u)^2/(2pq) (u <= p+q), 1 (u >= p+q). */
static void cdf_xy(arb_t out, double a, double b, double c, double d, const arf_t z, slong prec) {
    arf_t w1, w2, u, t, pp, qq;
    arf_init(w1); arf_init(w2); arf_init(u); arf_init(t); arf_init(pp); arf_init(qq);
    arf_dsub(w1, b, a); arf_dsub(w2, d, c);
    if (arf_is_zero(w1) && arf_is_zero(w2)) {
        arf_dsub(t, a, c);                                     /* X - Y = a - c */
        if (arf_cmp(t, z) <= 0) arb_one(out); else arb_zero(out);
    } else if (arf_is_zero(w1) || arf_is_zero(w2)) {
        /* X = a: F = P(Y >= a - z) = (d - a + z)/w2;  Y = c: F = P(X <= c + z) = (c - a + z)/w1 */
        if (arf_is_zero(w1)) arf_dsub(t, d, a); else arf_dsub(t, c, a);
        arf_add(t, t, z, ARF_PREC_EXACT, ARF_RND_DOWN);
        arf_srcptr w = arf_is_zero(w1) ? w2 : w1;
        if (arf_sgn(t) <= 0) arb_zero(out);
        else if (arf_cmp(t, w) >= 0) arb_one(out);
        else { arb_set_arf(out, t); arb_t ww; arb_init(ww); arb_set_arf(ww, w); arb_div(out, out, ww, prec); arb_clear(ww); }
    } else {
        if (arf_cmp(w1, w2) <= 0) { arf_set(pp, w1); arf_set(qq, w2); } else { arf_set(pp, w2); arf_set(qq, w1); }
        arf_dsub(u, d, a); arf_add(u, u, z, ARF_PREC_EXACT, ARF_RND_DOWN);       /* u = z - (a - d) */
        arf_add(t, pp, qq, ARF_PREC_EXACT, ARF_RND_DOWN);                         /* p + q */
        if (arf_sgn(u) <= 0) arb_zero(out);
        else if (arf_cmp(u, t) >= 0) arb_one(out);
        else {
            arb_t num, den; arb_init(num); arb_init(den);
            if (arf_cmp(u, pp) <= 0) {
                arb_set_arf(num, u); arb_sqr(num, num, prec);
                arb_set_arf(den, pp); arb_mul_arf(den, den, qq, prec); arb_mul_2exp_si(den, den, 1);
                arb_div(out, num, den, prec);
            } else if (arf_cmp(u, qq) <= 0) {
                arb_set_arf(num, u); arb_mul_2exp_si(num, num, 1); arb_sub_arf(num, num, pp, prec);
                arb_set_arf(den, qq); arb_mul_2exp_si(den, den, 1);
                arb_div(out, num, den, prec);
            } else {
                arf_sub(t, t, u, ARF_PREC_EXACT, ARF_RND_DOWN);                   /* p + q - u */
                arb_set_arf(num, t); arb_sqr(num, num, prec);
                arb_set_arf(den, pp); arb_mul_arf(den, den, qq, prec); arb_mul_2exp_si(den, den, 1);
                arb_div(out, num, den, prec); arb_sub_ui(out, out, 1, prec); arb_neg(out, out);
            }
            arb_clear(num); arb_clear(den);
        }
    }
    arf_clear(w1); arf_clear(w2); arf_clear(u); arf_clear(t); arf_clear(pp); arf_clear(qq);
}
/* lower bounds pin <= P(|U_i - U_j| <= 1), pout <= P(|U_i - U_j| > 1) for U_i, U_j independent uniform on the rectangles
   (BOUNDS.md 3c): Z = U_i - U_j has independent coordinates; 2^nstrip_log2 vertical strips of the support of Z_x;
   inside: strip x [-sqrt(1-amax^2), sqrt(1-amax^2)] (evaluated at the lower end of the sqrt ball; P(|Z_y|<=t) >= F(t)-F(-t));
   outside: P(|Z| <= 1) <= sum_strips P(Z_x in strip) P(|Z_y| <= sqrt(1-amin^2)) (upper end of the ball).  Z_x is always
   continuous here (a box never has zero width in r2 or xi), so strip endpoints carry no mass. */
static void prob_strips(arf_t pin_lb, arf_t pout_lb, int i, int j, const double *xl, const double *xh, const double *yl,
                        const double *yh, slong prec) {
    int ns = 1 << nstrip_log2;
    arf_t zx0, wz, xt[65], amax, amin, yb, nyb, t1, t2, one;
    arb_t F[65], px, G, Fa, Fb, pin, outer, s;
    arf_init(zx0); arf_init(wz); arf_init(amax); arf_init(amin); arf_init(yb); arf_init(nyb); arf_init(t1); arf_init(t2);
    arf_init(one); arf_one(one);
    arb_init(px); arb_init(G); arb_init(Fa); arb_init(Fb); arb_init(pin); arb_init(outer); arb_init(s);
    for (int t = 0; t <= ns; t++) { arf_init(xt[t]); arb_init(F[t]); }
    arf_dsub(zx0, xl[i], xh[j]); arf_dsub(wz, xh[i], xl[j]); arf_sub(wz, wz, zx0, ARF_PREC_EXACT, ARF_RND_DOWN);
    int ydeg = (yh[i] == yl[i] && yh[j] == yl[j]);
    arb_zero(pin); arb_zero(outer);
    if (arf_sgn(wz) <= 0) { arf_zero(pin_lb); arf_zero(pout_lb); goto done; }   /* not reached (Z_x continuous) */
    for (int t = 0; t <= ns; t++) {
        arf_mul_si(xt[t], wz, t, ARF_PREC_EXACT, ARF_RND_DOWN); arf_mul_2exp_si(xt[t], xt[t], -nstrip_log2);
        arf_add(xt[t], xt[t], zx0, ARF_PREC_EXACT, ARF_RND_DOWN);
        cdf_xy(F[t], xl[i], xh[i], xl[j], xh[j], xt[t], prec);
    }
    for (int t = 0; t < ns; t++) {
        arb_sub(px, F[t + 1], F[t], prec);
        arf_abs(t1, xt[t]); arf_abs(t2, xt[t + 1]);
        arf_max(amax, t1, t2);
        if (arf_sgn(xt[t]) <= 0 && arf_sgn(xt[t + 1]) >= 0) arf_zero(amin); else arf_min(amin, t1, t2);
        if (arf_cmp(amax, one) < 0) {
            arb_set_arf(s, amax); arb_sqr(s, s, prec); arb_sub_ui(s, s, 1, prec); arb_neg(s, s); arb_sqrt(s, s, prec);
            arb_get_lbound_arf(yb, s, prec);
            if (arf_sgn(yb) > 0) {
                arf_neg(nyb, yb);
                cdf_xy(Fb, yl[i], yh[i], yl[j], yh[j], yb, prec); cdf_xy(Fa, yl[i], yh[i], yl[j], yh[j], nyb, prec);
                arb_sub(G, Fb, Fa, prec); arb_mul(G, G, px, prec); arb_add(pin, pin, G, prec);
            }
        }
        if (arf_cmp(amin, one) < 0) {
            arb_set_arf(s, amin); arb_sqr(s, s, prec); arb_sub_ui(s, s, 1, prec); arb_neg(s, s); arb_sqrt(s, s, prec);
            arb_get_ubound_arf(yb, s, prec);
            if (ydeg) {                                   /* Z_y = yl_i - yl_j exactly */
                arf_dsub(t1, yl[i], yl[j]); arf_abs(t1, t1);
                if (arf_cmp(t1, yb) <= 0) arb_one(G); else arb_zero(G);
            } else {
                arf_neg(nyb, yb);
                cdf_xy(Fb, yl[i], yh[i], yl[j], yh[j], yb, prec); cdf_xy(Fa, yl[i], yh[i], yl[j], yh[j], nyb, prec);
                arb_sub(G, Fb, Fa, prec);
            }
            arb_mul(G, G, px, prec); arb_add(outer, outer, G, prec);
        }
    }
    arb_get_lbound_arf(pin_lb, pin, prec);
    if (arf_sgn(pin_lb) < 0) arf_zero(pin_lb);
    arb_sub_ui(s, outer, 1, prec); arb_neg(s, s);
    arb_get_lbound_arf(pout_lb, s, prec);
    if (arf_sgn(pout_lb) < 0) arf_zero(pout_lb);
done:
    arf_clear(zx0); arf_clear(wz); arf_clear(amax); arf_clear(amin); arf_clear(yb); arf_clear(nyb); arf_clear(t1); arf_clear(t2);
    arf_clear(one);
    arb_clear(px); arb_clear(G); arb_clear(Fa); arb_clear(Fb); arb_clear(pin); arb_clear(outer); arb_clear(s);
    for (int t = 0; t <= ns; t++) { arf_clear(xt[t]); arb_clear(F[t]); }
}

/* phi(t) = t^{-s}, s = k - 1/2: phi = sqrt(t)/t^k; phi' = -s phi/t; phi'' = s(s+1) phi/t^2 */
static void phi_all(arb_t f0, arb_t f1, arb_t f2, const arb_t t, slong prec) {
    arb_t u, sv; arb_init(u); arb_init(sv);
    arb_sqrt(u, t, prec); arb_pow_ui(f0, t, k, prec); arb_div(f0, u, f0, prec);
    arb_set_si(sv, 2 * k - 1); arb_mul_2exp_si(sv, sv, -1);                     /* s */
    if (f1) { arb_div(f1, f0, t, prec); arb_mul(f1, f1, sv, prec); arb_neg(f1, f1); }
    if (f2) { arb_div(f2, f0, t, prec); arb_div(f2, f2, t, prec); arb_mul(f2, f2, sv, prec); arb_add_ui(sv, sv, 1, prec);
              arb_mul(f2, f2, sv, prec); }
    arb_clear(u); arb_clear(sv);
}

/* ---------------- B6. the leaf (BOUNDS.md 3b, 3c, 3d as of box_ck13) ---------------- */
static void lbound_clip0(arf_t out, const arb_t x) { arb_get_lbound_arf(out, x, RPREC); if (arf_sgn(out) < 0) arf_zero(out); }

/* EV(q) = max(q fmin, val - (1 - q) fmax) >= (1/v) int_{Q cap E} r2 phi(A) for an event E with P(E) >= q, given
   fmin <= r2 phi(A(y)) <= fmax on Q and (1/v) int_Q r2 phi(A) >= val.  Inputs exact (arf), exact arithmetic. */
static void ev_lb(arf_t out, const arf_t q, const arf_t fmin, const arf_t fmax, const arf_t val) {
    arf_t a, t; arf_init(a); arf_init(t);
    arf_mul(a, q, fmin, ARF_PREC_EXACT, ARF_RND_DOWN);
    arf_one(t); arf_sub(t, t, q, ARF_PREC_EXACT, ARF_RND_DOWN);
    arf_mul(t, t, fmax, ARF_PREC_EXACT, ARF_RND_DOWN);
    arf_sub(t, val, t, ARF_PREC_EXACT, ARF_RND_DOWN);
    arf_max(out, a, t);
    if (arf_sgn(out) < 0) arf_zero(out);
    arf_clear(a); arf_clear(t);
}
/* 3c: best over T = {e} and T = {e, f} of sum over the joint states s of (g_s - gmin) EV(P_lo(E_s)) (2g units).  The joint
   states of T partition Q (up to the null sets |y_i - y_j| = 1); P_lo = staircase bound (single edge), product of the
   staircase bounds for two vertex-disjoint edges (independent points), Frechet max(0, P1 + P2 - 1) otherwise. */
static void extra_best(arf_t best, int nu, const int *ul, arf_srcptr pin, arf_srcptr pout, const int *gpres, const int *gabs,
                       const int *g2pair, int gmin, const arf_t fmin, const arf_t fmax, const arf_t val) {
    arf_t sc, e, q, one; arf_init(sc); arf_init(e); arf_init(q); arf_init(one); arf_one(one);
    arf_zero(best);
    for (int t = 0; t < nu; t++) {
        int p = ul[t];
        arf_zero(sc);
        if (gpres[p] > gmin) { ev_lb(e, pin + t, fmin, fmax, val); arf_mul_si(e, e, gpres[p] - gmin, ARF_PREC_EXACT, ARF_RND_DOWN); arf_add(sc, sc, e, ARF_PREC_EXACT, ARF_RND_DOWN); }
        if (gabs[p] > gmin) { ev_lb(e, pout + t, fmin, fmax, val); arf_mul_si(e, e, gabs[p] - gmin, ARF_PREC_EXACT, ARF_RND_DOWN); arf_add(sc, sc, e, ARF_PREC_EXACT, ARF_RND_DOWN); }
        if (arf_cmp(sc, best) > 0) arf_set(best, sc);
    }
    for (int t1 = 0; t1 < nu; t1++) for (int t2 = t1 + 1; t2 < nu; t2++) {
        int p1 = ul[t1], p2 = ul[t2];
        int disjoint = rpi[p1] != rpi[p2] && rpi[p1] != rpj[p2] && rpj[p1] != rpi[p2] && rpj[p1] != rpj[p2];
        if (mut_indep) disjoint = 1;                               /* negative control: pretend independence */
        arf_zero(sc);
        for (int s1 = 0; s1 <= 1; s1++) for (int s2 = 0; s2 <= 1; s2++) {
            int gs = g2pair[(t1 * PMAX + t2) * 4 + 2 * s1 + s2];
            if (gs <= gmin) continue;
            arf_srcptr q1 = s1 ? pin + t1 : pout + t1, q2 = s2 ? pin + t2 : pout + t2;
            if (disjoint) arf_mul(q, q1, q2, ARF_PREC_EXACT, ARF_RND_DOWN);
            else { arf_add(q, q1, q2, ARF_PREC_EXACT, ARF_RND_DOWN); arf_sub(q, q, one, ARF_PREC_EXACT, ARF_RND_DOWN); if (arf_sgn(q) < 0) arf_zero(q); }
            ev_lb(e, q, fmin, fmax, val); arf_mul_si(e, e, gs - gmin, ARF_PREC_EXACT, ARF_RND_DOWN); arf_add(sc, sc, e, ARF_PREC_EXACT, ARF_RND_DOWN);
        }
        if (arf_cmp(sc, best) > 0) arf_set(best, sc);
    }
    arf_clear(sc); arf_clear(e); arf_clear(q); arf_clear(one);
}

static void chk_leaf(const Box *b, const FInfo *fi0) {
    RAcc *ra = tl_racc;
    FInfo fcopy; const FInfo *fi = fi0;
    if (mut_flt) { fcopy = *fi0; fcopy.flt *= 1.01; fi = &fcopy; }   /* control: a float code overstating every leaf by 1% */
    ra->nleaf++; ra->flt_sum += fi->flt;
    if (skip_zero_flt && fi->flt == 0) { ra->nskip++; return; }   /* skipping a leaf can only lower the certified sum */
    const slong prec = RPREC;
    double xl[KMAX], xh[KMAX], yl[KMAX], yh[KMAX], xc[KMAX], yc[KMAX], h[DMAX];
    /* BOUNDS.md section 2: x = (r2, xi_2, eta_2, ..., xi_{k-1}, eta_{k-1}); y_0 = 0, y_1 = (r2, 0), y_j = (xi_j, eta_j) */
    xl[0] = xh[0] = yl[0] = yh[0] = 0;
    xl[1] = b->lo[0]; xh[1] = b->hi[0]; yl[1] = yh[1] = 0;
    for (int j = 2; j < k; j++) { xl[j] = b->lo[2 * j - 3]; xh[j] = b->hi[2 * j - 3]; yl[j] = b->lo[2 * j - 2]; yh[j] = b->hi[2 * j - 2]; }
    int centre_ok = 1;
    arf_t e1, e2, e3;
    arf_init(e1); arf_init(e2); arf_init(e3);
    for (int i = 0; i < k; i++) {                         /* centres must be exact midpoints (E delta = 0) */
        xc[i] = 0.5 * (xl[i] + xh[i]); yc[i] = 0.5 * (yl[i] + yh[i]);
        arf_set_d(e1, xl[i]); arf_set_d(e2, xh[i]); arf_add(e1, e1, e2, ARF_PREC_EXACT, ARF_RND_DOWN);
        arf_set_d(e3, xc[i]); arf_mul_2exp_si(e3, e3, 1); if (!arf_equal(e1, e3)) centre_ok = 0;
        arf_set_d(e1, yl[i]); arf_set_d(e2, yh[i]); arf_add(e1, e1, e2, ARF_PREC_EXACT, ARF_RND_DOWN);
        arf_set_d(e3, yc[i]); arf_mul_2exp_si(e3, e3, 1); if (!arf_equal(e1, e3)) centre_ok = 0;
    }
    for (int d = 0; d < m; d++) {                         /* widths must be exact (volume, moments) */
        h[d] = b->hi[d] - b->lo[d];
        arf_dsub(e1, b->hi[d], b->lo[d]); arf_set_d(e2, h[d]); if (!arf_equal(e1, e2) || !(h[d] > 0)) centre_ok = 0;
    }
    arf_clear(e1); arf_clear(e2); arf_clear(e3);
    /* domain: r2 >= 0, eta_2 >= 0, and the xi order (Q inside D, or exactly one straddling pair) */
    int nstr = 0, spair = -1, outside = (b->lo[0] < 0) || (k >= 3 && yl[2] < 0) || !centre_ok;
    for (int j = 2; j + 1 < k; j++) { if (xl[j] > xh[j + 1]) outside = 1; else if (xh[j] > xl[j + 1]) { nstr++; spair = j; } }
    if (!centre_ok) ra->ncentre_bad++;
    /* B2: exact edge classes */
    int state[PMAX];
    long long pres = 0, und = 0;
    arb_t d2mn[PMAX], d2mx[PMAX];
    {
        arf_t dmin2, dmax2, one; arf_init(dmin2); arf_init(dmax2); arf_init(one); arf_one(one);
        for (int p = 0; p < rnp; p++) {
            exact_d2(dmin2, dmax2, rpi[p], rpj[p], xl, xh, yl, yh);
            arb_init(d2mn[p]); arb_init(d2mx[p]); arb_set_arf(d2mn[p], dmin2); arb_set_arf(d2mx[p], dmax2);
            if (arf_cmp(dmax2, one) <= 0) state[p] = 1;          /* present: d^+ <= 1 */
            else if (arf_cmp(dmin2, one) > 0) state[p] = 0;      /* absent: d^- > 1 */
            else state[p] = mut_class ? 1 : 2;                   /* undetermined (mut_class: negative control) */
            if (state[p] == 1) pres |= 1LL << p; else if (state[p] == 2) und |= 1LL << p;
        }
        arf_clear(dmin2); arf_clear(dmax2); arf_clear(one);
    }
    /* B1: g bounds over completions (single undetermined edges and pairs of them) */
    int gmin, gmax, gp[PMAX], ga[PMAX], ul[PMAX], nu, g2pair[PMAX * PMAX * 4];
    own_g_bounds2(state, &gmin, &gmax, gp, ga, ul, &nu, g2pair);
    int classdiff = (pres != fi->pres || und != fi->und || gmin != fi->gmin || gmax != fi->gmax);
    if (classdiff) ra->nclassdiff++;
    int need_extra = (!outside && nstr == 0 && gmin < gmax && gmax > 0);
    int need_int = (!outside && nstr == 0 && gmin > 0), need_str = (!outside && nstr == 1 && gmin > 0);
    arf_t lb_main, lb_tight;
    arf_init(lb_main); arf_init(lb_tight);
    int zero = 0, tmin_ok = 0, nvdiff = 0;
    /* 3e: some pair with d^- = 0 (two centres can coincide): Lemma V is not used; A(y) <= union area of B(c_i, 1 + delta),
       delta = max_i del_i; contribution v gmin r2_lo phi(A_enl) if gmin > 0 and the box is not order-straddling. */
    int enl_case = 0;
    for (int p = 0; p < rnp; p++) if (arb_is_zero(d2mn[p])) enl_case = 1;
    if (enl_case != fi->enl) ra->nenl_diff++;
    if (enl_case) {
        ra->nenl++;
        if (!(!outside && nstr == 0 && gmin > 0 && b->lo[0] > 0)) { ra->nfast0++; goto account; }
        double t0e = omp_get_wtime();
        ra->narb++; ra->flt_eval += fi->flt;
        arb_t t, u, delta, Aenl, v; arf_t Rhi, Ahi;
        arb_init(t); arb_init(u); arb_init(delta); arb_init(Aenl); arb_init(v); arf_init(Rhi); arf_init(Ahi);
        arb_zero(delta);
        for (int i = 0; i < k; i++) {                 /* del_i = half diagonal of R_i (exact widths) */
            arb_set_d(t, xh[i]); arb_set_d(u, xl[i]); arb_sub(t, t, u, prec); arb_sqr(t, t, prec);
            arb_set_d(u, yh[i]); arb_set_d(Aenl, yl[i]); arb_sub(u, u, Aenl, prec); arb_sqr(u, u, prec);
            arb_add(t, t, u, prec); arb_sqrt(t, t, prec); arb_mul_2exp_si(t, t, -1);
            arb_max(delta, delta, t, prec);
        }
        arb_add_ui(t, delta, 1, prec); arb_get_ubound_arf(Rhi, t, prec);   /* R_hi >= 1 + delta (area is increasing in R) */
        if (mut_enl1) arf_one(Rhi);                                            /* negative control (invalid) */
        if (rig_union_R(Aenl, xc, yc, Rhi, prec) != 0) { zero = 1; }
        else {
            arb_get_ubound_arf(Ahi, Aenl, prec); arb_set_arf(t, Ahi);         /* upper bound of A_enl */
            phi_all(u, NULL, NULL, t, prec);
            arb_one(v); for (int d = 0; d < m; d++) { arb_set_d(t, h[d]); arb_mul(v, v, t, prec); }
            arb_mul(u, u, v, prec); arb_set_d(t, b->lo[0]); arb_mul(u, u, t, prec); arb_mul_si(u, u, gmin, prec);
            arb_mul_2exp_si(u, u, -1);
            lbound_clip0(lb_main, u); arf_set(lb_tight, lb_main);
        }
        arb_clear(t); arb_clear(u); arb_clear(delta); arb_clear(Aenl); arb_clear(v); arf_clear(Rhi); arf_clear(Ahi);
        ra->t_arb += omp_get_wtime() - t0e;
        goto account;
    }
    if (!(need_int || need_extra || need_str)) { ra->nfast0++; goto account; }
    double t0 = omp_get_wtime();
    ra->narb++; ra->flt_eval += fi->flt;
    {
        arb_t A, gxv[KMAX], gyv[KMAX], bv[DMAX], Rmax, Er, sEr2, t, u, w, v, sumb, Sb, tmin, a2, f0, f1, f2, f1A, g2, fmin_pt;
        arb_t fmax_pt, Er2, valA2, valB2, hd, r2c;
        arb_init(A); arb_init(Rmax); arb_init(Er); arb_init(sEr2); arb_init(t); arb_init(u); arb_init(w); arb_init(v);
        arb_init(sumb); arb_init(Sb); arb_init(tmin); arb_init(a2); arb_init(f0); arb_init(f1); arb_init(f2); arb_init(f1A);
        arb_init(g2); arb_init(fmin_pt); arb_init(fmax_pt); arb_init(Er2); arb_init(valA2); arb_init(valB2); arb_init(hd);
        arb_init(r2c);
        for (int i = 0; i < k; i++) { arb_init(gxv[i]); arb_init(gyv[i]); }
        for (int d = 0; d < m; d++) arb_init(bv[d]);
        arf_t fminL, fmaxU, valM, valT, xlb, xlbT, elb, elbT, best;
        arf_init(fminL); arf_init(fmaxU); arf_init(valM); arf_init(valT); arf_init(xlb); arf_init(xlbT); arf_init(elb);
        arf_init(elbT); arf_init(best);
        int nv[PMAX];
        if (rig_union(A, (arb_ptr) gxv, (arb_ptr) gyv, xc, yc, prec) != 0) { zero = 1; goto cleanup; }
        if (rig_remainder(Rmax, Er, sEr2, nv, xl, xh, yl, yh, xc, yc, d2mn[0], d2mx[0], prec) != 0) { zero = 1; goto cleanup; }
        for (int p = 0; p < rnp; p++) if (nv[p] != fi->nv[p] && !(arf_cmp_si(arb_midref(d2mn[p]), 4) >= 0)) nvdiff = 1;
        if (nvdiff) ra->nnvdiff++;
        {   /* diagnostics: agreement of A and E r with the float code */
            double dA = fabs(arf_get_d(arb_midref(A), ARF_RND_NEAR) - fi->A);
            if (dA > ra->maxAdiff) ra->maxAdiff = dA;
            if (dA > 1e-9) ra->nAdiff++;
            if (!nvdiff) { double dE = fabs(arf_get_d(arb_midref(Er), ARF_RND_NEAR) - fi->Er); if (dE > ra->maxEdiff) ra->maxEdiff = dE; }
        }
        /* gradient in box coordinates: b_0 = dA/d(y_1)_x, b_{2j-3} = dA/d(y_j)_x, b_{2j-2} = dA/d(y_j)_y */
        arb_set(bv[0], gxv[1]);
        for (int j = 2; j < k; j++) { arb_set(bv[2 * j - 3], gxv[j]); arb_set(bv[2 * j - 2], gyv[j]); }
        arb_zero(sumb); arb_zero(Sb);
        for (int d = 0; d < m; d++) {
            arb_set_d(hd, h[d]);
            arb_abs(t, bv[d]); arb_mul(t, t, hd, prec); arb_mul_2exp_si(t, t, -1); arb_add(sumb, sumb, t, prec);
            arb_mul(t, bv[d], hd, prec); arb_sqr(t, t, prec); arb_div_ui(t, t, 12, prec); arb_add(Sb, Sb, t, prec);
        }
        arb_one(v);
        for (int d = 0; d < m; d++) { arb_set_d(hd, h[d]); arb_mul(v, v, hd, prec); }
        /* pointwise bounds (3c): A(c) - sum|b|h/2 - Rmax <= A(y) <= A(c) + sum|b|h/2 + Rmax (two-sided Lemma V), A(y) >= pi;
           fmin_pt = r2_lo phi(upper), fmax_pt = r2_hi phi(max(pi, lower)) */
        arb_add(t, A, sumb, prec); arb_add(t, t, Rmax, prec);
        phi_all(f0, NULL, NULL, t, prec);
        arb_set_d(u, b->lo[0]); arb_mul(fmin_pt, f0, u, prec);
        lbound_clip0(fminL, fmin_pt);
        arb_sub(t, A, sumb, prec); arb_sub(t, t, Rmax, prec); arb_const_pi(u, prec); arb_max(t, t, u, prec);
        phi_all(f0, NULL, NULL, t, prec);
        arb_set_d(u, b->hi[0]); arb_mul(fmax_pt, f0, u, prec);
        arb_get_ubound_arf(fmaxU, fmax_pt, prec);
        if (mut_fmaxlo) arf_set(fmaxU, fminL);                         /* negative control: wrong (too small) fmax_pt */
        /* 3b: val = lower bound of (1/v) int_Q r2 phi(A) (0 unless tmin > 0 certainly) */
        arf_zero(valM); arf_zero(valT);
        arb_sub(tmin, A, sumb, prec);
        tmin_ok = arb_is_positive(tmin);
        if (tmin_ok) {
            arb_add(a2, A, Er, prec);                              /* A(c) + Er, Er >= E r */
            arb_sqr(Er2, sEr2, prec);                              /* Er2 >= E r^2 */
            phi_all(f0, f1, NULL, a2, prec);                       /* phi(A + Er), phi'(A + Er) */
            phi_all(t, NULL, f2, tmin, prec);                      /* phi''(tmin) */
            phi_all(t, f1A, NULL, A, prec);                        /* phi'(A(c)) */
            arb_set_d(hd, h[0]);
            arb_set_d(r2c, xc[1]);                                 /* centre of r2 (checked exact) */
            arb_sqr(t, hd, prec); arb_mul(t, t, bv[0], prec); arb_div_ui(t, t, 12, prec);   /* b_0 h_0^2/12 */
            arb_sqrt(g2, Sb, prec);                                /* sqrt(sum_d b_d^2 h_d^2/12) */
            /* BOUNDS.md 3b (headline): r2c phi(A + Er) + phi'(A) b_0 h_0^2/12 - |phi'(A)| (h_0/2) Er
                                         - (h_0/4) phi''(tmin) (sqrt(Sb) + sqrt(Er2))^2 */
            arb_mul(valB2, f1A, t, prec);
            arb_mul(u, r2c, f0, prec); arb_add(valB2, valB2, u, prec);
            arb_mul(u, hd, Er, prec); arb_mul(u, u, f1A, prec); arb_mul_2exp_si(u, u, -1); arb_add(valB2, valB2, u, prec);
            arb_add(w, g2, sEr2, prec); arb_sqr(w, w, prec); arb_mul(w, w, f2, prec);
            arb_mul(w, w, hd, prec); arb_mul_2exp_si(w, w, -2); arb_sub(valB2, valB2, w, prec);
            /* extra info (also valid): expansion at A + Er with E(X - A - Er)^2 <= (sqrt Sb + sqrt(Er2 + Er^2))^2 */
            arb_mul(valA2, f1, t, prec);
            arb_mul(u, r2c, f0, prec); arb_add(valA2, valA2, u, prec);
            arb_mul(u, hd, Er, prec); arb_mul(u, u, f1, prec); arb_mul_2exp_si(u, u, -1); arb_add(valA2, valA2, u, prec);
            arb_sqr(w, Er, prec); arb_add(w, w, Er2, prec); arb_sqrt(w, w, prec);
            arb_add(w, w, g2, prec); arb_sqr(w, w, prec); arb_mul(w, w, f2, prec); arb_mul(w, w, hd, prec);
            arb_mul_2exp_si(w, w, -2); arb_sub(valA2, valA2, w, prec);
            if (mut_old3b) {   /* negative control: the pre-correction formula (not justified) as the headline */
                arb_mul(u, hd, Er, prec); arb_add(u, u, t, prec); arb_mul(valB2, f1, u, prec);
                arb_mul(u, r2c, f0, prec); arb_add(valB2, valB2, u, prec);
                arb_add(w, Sb, Er2, prec); arb_mul(w, w, f2, prec); arb_mul(w, w, hd, prec); arb_mul_2exp_si(w, w, -1);
                arb_sub(valB2, valB2, w, prec);
            }
            lbound_clip0(valM, valB2);
            lbound_clip0(valT, valA2); arf_max(valT, valT, valM);
        }
        if (need_int) {                                            /* gmin v val (3b, also the gmin part of 3c) */
            arb_mul_si(t, v, gmin, prec); arb_mul_2exp_si(t, t, -1);
            arb_mul_arf(u, t, valM, prec); lbound_clip0(xlb, u);
            arb_mul_arf(u, t, valT, prec); lbound_clip0(xlbT, u);
        }
        if (need_extra) {                                          /* 3c extras: v * best/2 */
            arf_struct pin[PMAX], pout[PMAX];
            for (int t1 = 0; t1 < nu; t1++) {
                arf_init(pin + t1); arf_init(pout + t1);
                prob_strips(pin + t1, pout + t1, rpi[ul[t1]], rpj[ul[t1]], xl, xh, yl, yh, prec);
            }
            extra_best(best, nu, ul, pin, pout, gp, ga, g2pair, gmin, fminL, fmaxU, valM);
            arb_mul_arf(t, v, best, prec); arb_mul_2exp_si(t, t, -1); lbound_clip0(elb, t);
            extra_best(best, nu, ul, pin, pout, gp, ga, g2pair, gmin, fminL, fmaxU, valT);
            arb_mul_arf(t, v, best, prec); arb_mul_2exp_si(t, t, -1); lbound_clip0(elbT, t);
            for (int t1 = 0; t1 < nu; t1++) { arf_clear(pin + t1); arf_clear(pout + t1); }
        }
        if (need_str) {                                            /* 3d: v gmin EV(P(xi_j <= xi_{j+1})) (2g/2) */
            arf_t z0, pord, ev; arf_init(z0); arf_init(pord); arf_init(ev); arf_zero(z0);
            cdf_xy(u, xl[spair], xh[spair], xl[spair + 1], xh[spair + 1], z0, prec);
            lbound_clip0(pord, u);
            if (mut_order) arf_one(pord);                          /* negative control: ignore the ordering constraint */
            arb_mul_si(t, v, gmin, prec); arb_mul_2exp_si(t, t, -1);
            ev_lb(ev, pord, fminL, fmaxU, valM); arb_mul_arf(u, t, ev, prec); lbound_clip0(elb, u);
            ev_lb(ev, pord, fminL, fmaxU, valT); arb_mul_arf(u, t, ev, prec); lbound_clip0(elbT, u);
            arf_clear(z0); arf_clear(pord); arf_clear(ev);
        }
        arf_add(lb_main, xlb, elb, ARF_PREC_EXACT, ARF_RND_DOWN);
        arf_add(lb_tight, xlbT, elbT, ARF_PREC_EXACT, ARF_RND_DOWN);
    cleanup:
        arf_clear(fminL); arf_clear(fmaxU); arf_clear(valM); arf_clear(valT); arf_clear(xlb); arf_clear(xlbT); arf_clear(elb);
        arf_clear(elbT); arf_clear(best);
        arb_clear(A); arb_clear(Rmax); arb_clear(Er); arb_clear(sEr2); arb_clear(t); arb_clear(u); arb_clear(w); arb_clear(v);
        arb_clear(sumb); arb_clear(Sb); arb_clear(tmin); arb_clear(a2); arb_clear(f0); arb_clear(f1); arb_clear(f2);
        arb_clear(f1A); arb_clear(g2); arb_clear(fmin_pt); arb_clear(fmax_pt); arb_clear(Er2); arb_clear(valA2);
        arb_clear(valB2); arb_clear(hd); arb_clear(r2c);
        for (int i = 0; i < k; i++) { arb_clear(gxv[i]); arb_clear(gyv[i]); }
        for (int d = 0; d < m; d++) arb_clear(bv[d]);
    }
    ra->t_arb += omp_get_wtime() - t0;
account:;
    arb_add_arf(ra->sum_main, ra->sum_main, lb_main, prec);
    arb_add_arf(ra->sum_tight, ra->sum_tight, lb_tight, prec);
    double rm = arf_get_d(lb_main, ARF_RND_DOWN);
    if (rm == 0) ra->nrig0++;
    if (rm > 1.001 * fi->flt + 1e-300) ra->nabove++;
    if (fi->flt > 0 && rm < 0.999 * fi->flt) {
        int r;
        if (classdiff) r = R_CLASS;
        else if (zero || outside) r = R_ZERO;
        else if (fi->tmin > 0 && !tmin_ok) r = R_TMIN;
        else if (nvdiff) r = R_PRUNE;
        else r = R_OTHER;
        ra->nbelow++; ra->reason[r]++; ra->reason_flt[r] += fi->flt; ra->reason_rig[r] += rm;
    }
    arf_clear(lb_main); arf_clear(lb_tight);
    for (int p = 0; p < rnp; p++) { arb_clear(d2mn[p]); arb_clear(d2mx[p]); }
}

/* ======================================================================================================================
 * Part C: driver, self-tests
 * ==================================================================================================================== */
static void print_lower(const char *label, const arb_t x) {   /* prints floor(1e10 * lower(x)) / 1e10 (certified) */
    arf_t lo; fmpz_t z; arf_init(lo); fmpz_init(z);
    arb_get_lbound_arf(lo, x, RPREC);
    arf_mul_ui(lo, lo, 10000000000UL, ARF_PREC_EXACT, ARF_RND_DOWN);
    arf_get_fmpz(z, lo, ARF_RND_FLOOR);
    slong zz = fmpz_get_si(z);
    if (zz < 0) printf("%s -%ld.%010ld\n", label, (-zz) / 10000000000L, (-zz) % 10000000000L);
    else printf("%s %ld.%010ld\n", label, zz / 10000000000L, zz % 10000000000L);
    arf_clear(lo); fmpz_clear(z);
}
static void prefactor(arb_t P, slong prec) {                  /* 2 pi Gamma(k - 1/2) (k-2)! / k! */
    arb_t g, x; arb_init(g); arb_init(x);
    arb_const_pi(P, prec); arb_mul_2exp_si(P, P, 1);
    arb_set_si(x, 2 * k - 1 + (mut_pref ? 2 : 0)); arb_mul_2exp_si(x, x, -1);   /* mut_pref: Gamma(k + 1/2) (control) */
    arb_gamma(g, x, prec); arb_mul(P, P, g, prec);
    if (!mut_orderfac) { arb_fac_ui(g, k - 2, prec); arb_mul(P, P, g, prec); }
    arb_fac_ui(g, k, prec); arb_div(P, P, g, prec);
    arb_clear(g); arb_clear(x);
}
static void init_proxy_circle(void) {
    arb_t t, u; arb_init(t); arb_init(u);
    TPR = 2 * M_PI;
    arb_const_pi(t, 256); arb_mul_2exp_si(t, t, 1); arb_set_d(u, TPR); arb_sub(t, t, u, 256);
    mag_init(EPS_TPR); abs_ub_mag(EPS_TPR, t);
    arb_clear(t); arb_clear(u);
}

/* ---- self-tests: rigorous union area vs the float code, CDF vs the float code and Monte Carlo, staircase vs MC ---- */
static double rnd_dyadic(unsigned long long *st, double lo, double hi, int bits) {
    *st = *st * 6364136223846793005ULL + 1442695040888963407ULL;
    double u = (double)((*st >> 20) & ((1ULL << bits) - 1)) / (double)(1ULL << bits);
    return lo + (hi - lo) * u;           /* dyadic if lo, hi, hi - lo are dyadic */
}
static double urand(unsigned long long *st) { *st = *st * 6364136223846793005ULL + 1442695040888963407ULL; return (double)(*st >> 11) / 9007199254740992.0; }
static int selftest(int argc, char **argv) {   /* (box_ck14 tables) */
    k = argc > 2 ? atoi(argv[2]) : 4; int N = argc > 3 ? atoi(argv[3]) : 2000;
    m = 2 * k - 3; s_exp = k - 0.5;
    build_tables(); own_build_g(); init_proxy_circle();
    long long ng = 1LL << rnp, mism = 0;
    for (long long E = 0; E < ng; E++) if (g2own[E] != g2tab[E]) mism++;
    printf("selftest k=%d: g table mismatches vs box_ck14: %lld of %lld\n", k, mism, ng);
    unsigned long long st = 12345;
    slong prec = RPREC;
    /* (1) union area and gradient */
    double maxdA = 0, maxdg = 0, maxrad = 0; int fails = 0, outside_ball = 0;
    for (int it = 0; it < N; it++) {
        double xc[KMAX], yc[KMAX], gx[KMAX], gy[KMAX];
        xc[0] = yc[0] = 0;
        for (int i = 1; i < k; i++) { xc[i] = rnd_dyadic(&st, -2, 2, 22); yc[i] = (i == 1) ? 0 : rnd_dyadic(&st, -2, 2, 22); }
        if (it % 7 == 0 && k >= 4) { xc[3] = xc[2] + 1.0; yc[3] = yc[2]; }              /* exact unit distance (tangent arcs) */
        if (it % 11 == 0 && k >= 4) { xc[3] = xc[2] + 2.0; yc[3] = yc[2]; }             /* exact distance 2 */
        if (it % 13 == 0) { xc[1] = 1.0; }                                                /* points 0, 1 at distance 1 */
        double Af = union_area_grad(xc, yc, gx, gy);
        arb_t A, gxa[KMAX], gya[KMAX]; arb_init(A);
        for (int i = 0; i < k; i++) { arb_init(gxa[i]); arb_init(gya[i]); }
        if (rig_union(A, (arb_ptr) gxa, (arb_ptr) gya, xc, yc, prec) != 0) fails++;
        else {
            double d = fabs(arf_get_d(arb_midref(A), ARF_RND_NEAR) - Af); if (d > maxdA) maxdA = d;
            double r = mag_get_d(arb_radref(A)); if (r > maxrad) maxrad = r;
            arb_t fv; arb_init(fv); arb_set_d(fv, Af);
            if (!arb_overlaps(A, fv) && d > 1e-12) outside_ball++;
            for (int i = 0; i < k; i++) {
                double d1 = fabs(arf_get_d(arb_midref(gxa[i]), ARF_RND_NEAR) - gx[i]);
                double d2 = fabs(arf_get_d(arb_midref(gya[i]), ARF_RND_NEAR) - gy[i]);
                if (d1 > maxdg) maxdg = d1;
                if (d2 > maxdg) maxdg = d2;
            }
            arb_clear(fv);
        }
        arb_clear(A); for (int i = 0; i < k; i++) { arb_clear(gxa[i]); arb_clear(gya[i]); }
    }
    printf("(1) union area: %d configs, %d rigorous failures (coincident), max |A_arb - A_float| = %.3g, max |grad diff| = %.3g, "
           "max ball radius = %.3g, float value farther than 1e-12 outside ball: %d\n", N, fails, maxdA, maxdg, maxrad, outside_ball);
    /* (1b) Monte Carlo check of the rigorous area for a few configurations */
    for (int it = 0; it < 3; it++) {
        double xc[KMAX], yc[KMAX];
        xc[0] = yc[0] = 0;
        for (int i = 1; i < k; i++) { xc[i] = rnd_dyadic(&st, -1.5, 1.5, 20); yc[i] = (i == 1) ? 0 : rnd_dyadic(&st, -1.5, 1.5, 20); }
        arb_t A, gxa[KMAX], gya[KMAX]; arb_init(A);
        for (int i = 0; i < k; i++) { arb_init(gxa[i]); arb_init(gya[i]); }
        rig_union(A, (arb_ptr) gxa, (arb_ptr) gya, xc, yc, prec);
        double xmin = 1e9, xmax = -1e9, ymin = 1e9, ymax = -1e9;
        for (int i = 0; i < k; i++) { xmin = fmin(xmin, xc[i] - 1); xmax = fmax(xmax, xc[i] + 1); ymin = fmin(ymin, yc[i] - 1); ymax = fmax(ymax, yc[i] + 1); }
        long long hit = 0, NS = 4000000;
        for (long long s = 0; s < NS; s++) {
            double px = xmin + (xmax - xmin) * urand(&st), py = ymin + (ymax - ymin) * urand(&st);
            for (int i = 0; i < k; i++) { double dx = px - xc[i], dy = py - yc[i]; if (dx * dx + dy * dy <= 1) { hit++; break; } }
        }
        double box = (xmax - xmin) * (ymax - ymin), mc = box * hit / (double)NS, se = box * sqrt((double)hit * (NS - hit) / NS) / NS;
        printf("(1b) MC area check %d: arb %.8f  MC %.6f +- %.6f  (%.1f sigma)\n", it, arf_get_d(arb_midref(A), ARF_RND_NEAR), mc, se,
               (arf_get_d(arb_midref(A), ARF_RND_NEAR) - mc) / se);
        arb_clear(A); for (int i = 0; i < k; i++) { arb_clear(gxa[i]); arb_clear(gya[i]); }
    }
    /* (1c) enlarged-disk union area (3e) vs R^2 * float union area at c/R, including identical centres */
    {
        double maxd = 0; int fl = 0;
        for (int it = 0; it < N; it++) {
            double xc[KMAX], yc[KMAX], xs[KMAX], ys[KMAX], gx[KMAX], gy[KMAX];
            xc[0] = yc[0] = 0;
            for (int i = 1; i < k; i++) { xc[i] = rnd_dyadic(&st, -2, 2, 12); yc[i] = (i == 1) ? 0 : rnd_dyadic(&st, -2, 2, 12); }
            if (it % 3 == 0) { xc[1] = 0; }                                  /* centre 1 = centre 0 */
            if (it % 5 == 0 && k >= 4) { xc[3] = xc[2]; yc[3] = yc[2]; }     /* centre 3 = centre 2 */
            double Rd = 1 + rnd_dyadic(&st, 0, 0.5, 10);
            for (int i = 0; i < k; i++) { xs[i] = xc[i] / Rd; ys[i] = yc[i] / Rd; }
            double Af = Rd * Rd * union_area_grad(xs, ys, gx, gy);
            arb_t A; arf_t Rx; arb_init(A); arf_init(Rx); arf_set_d(Rx, Rd);
            if (rig_union_R(A, xc, yc, Rx, prec) != 0) fl++;
            else { double d = fabs(arf_get_d(arb_midref(A), ARF_RND_NEAR) - Af); if (d > maxd) maxd = d; }
            arb_clear(A); arf_clear(Rx);
        }
        printf("(1c) enlarged-disk area: %d configs (with identical centres), %d failures, max |A_arb - R^2 A_float(c/R)| = %.3g\n", N, fl, maxd);
    }
    /* (2) CDF of differences of uniforms vs the float code */
    double maxdc = 0;
    for (int it = 0; it < 20 * N; it++) {
        double a = rnd_dyadic(&st, -2, 2, 12), b = a + ((it % 5 == 0) ? 0 : rnd_dyadic(&st, 0, 1, 10));
        double c = rnd_dyadic(&st, -2, 2, 12), d = c + ((it % 7 == 0) ? 0 : rnd_dyadic(&st, 0, 1, 10));
        double z = rnd_dyadic(&st, -4, 4, 16);
        arf_t zz; arf_init(zz); arf_set_d(zz, z);
        arb_t F; arb_init(F); cdf_xy(F, a, b, c, d, zz, prec);
        double ff = cdf_diff(a, b, c, d, z), dd = fabs(arf_get_d(arb_midref(F), ARF_RND_NEAR) - ff);
        if (dd > maxdc) maxdc = dd;
        arf_clear(zz); arb_clear(F);
    }
    printf("(2) CDF: max |F_arb - F_float| = %.3g over %d random (incl. degenerate) cases\n", maxdc, 20 * N);
    /* (3) staircase bounds vs Monte Carlo */
    int viol = 0; double worst = 0;
    for (int it = 0; it < 40; it++) {
        double xl[KMAX], xh[KMAX], yl[KMAX], yh[KMAX];
        int i = it % 3 == 0 ? 0 : 1, j = 2;
        xl[0] = xh[0] = yl[0] = yh[0] = 0;
        xl[1] = rnd_dyadic(&st, 0, 1.5, 10); xh[1] = xl[1] + rnd_dyadic(&st, 0.0625, 0.5, 6); yl[1] = yh[1] = 0;
        if (it % 5 == 0) { i = 0; j = 1; }
        xl[2] = rnd_dyadic(&st, -1.5, 1.5, 10); xh[2] = xl[2] + rnd_dyadic(&st, 0.0625, 0.5, 6);
        yl[2] = rnd_dyadic(&st, -1.5, 1.5, 10); yh[2] = yl[2] + rnd_dyadic(&st, 0.0625, 0.5, 6);
        arf_t pin, pout; arf_init(pin); arf_init(pout);
        prob_strips(pin, pout, i, j, xl, xh, yl, yh, prec);
        long long in = 0, NS = 2000000;
        for (long long s = 0; s < NS; s++) {
            double ax = xl[i] + (xh[i] - xl[i]) * urand(&st), ay = yl[i] + (yh[i] - yl[i]) * urand(&st);
            double bx = xl[j] + (xh[j] - xl[j]) * urand(&st), by = yl[j] + (yh[j] - yl[j]) * urand(&st);
            if ((ax - bx) * (ax - bx) + (ay - by) * (ay - by) <= 1) in++;
        }
        double pmc = in / (double)NS, se = sqrt(pmc * (1 - pmc) / NS) + 1e-12;
        double vin = (arf_get_d(pin, ARF_RND_NEAR) - pmc) / se, vout = (arf_get_d(pout, ARF_RND_NEAR) - (1 - pmc)) / se;
        if (vin > 4 || vout > 4) viol++;
        if (vin > worst) worst = vin;
        if (vout > worst) worst = vout;
        double pinf, poutf; prob_unit(xl[i], xh[i], yl[i], yh[i], xl[j], xh[j], yl[j], yh[j], &pinf, &poutf);
        if (it < 6) printf("(3) pair (%d,%d): pin %.6f (float %.6f) <= P_MC %.6f; pout %.6f (float %.6f) <= 1-P_MC %.6f\n", i, j,
                           arf_get_d(pin, ARF_RND_NEAR), pinf, pmc, arf_get_d(pout, ARF_RND_NEAR), poutf, 1 - pmc);
        arf_clear(pin); arf_clear(pout);
    }
    printf("(3) staircase: 40 cases, %d with a bound more than 4 sigma above MC (worst %.2f sigma)\n", viol, worst);
    return 0;
}

#ifndef CHK_BUILD
#define CHK_BUILD "unknown"
#endif
/* ---- combine shard outputs: chk_ck14 --combine FILE...  (sums the exact shard lower bounds, checks the shards) ---- */
typedef struct { int k; double W0, WF, EPS; long long ninit, nb, lo, hi; char build[64], mut[64]; char smain[128], stight[128];
                 double flt; long long scored, narb, nbelow; } ShardRec;
static int combine(int argc, char **argv) {
    ShardRec *S = malloc(sizeof(ShardRec) * 100000); int ns = 0;
    for (int a = 2; a < argc; a++) {
        FILE *f = fopen(argv[a], "r"); if (!f) { fprintf(stderr, "cannot open %s\n", argv[a]); return 1; }
        char line[4096];
        while (fgets(line, sizeof line, f)) {
            if (strncmp(line, "SHARD ", 6)) continue;
            ShardRec r; memset(&r, 0, sizeof r);
            int n = sscanf(line, "SHARD k=%d W0=%lg WF=%lg EPS=%lg ninit=%lld nb=%lld lo=%lld hi=%lld build=%63s mutate=%63s "
                                 "main_floor1e30=%127s tight_floor1e30=%127s flt_sum=%lg scored=%lld narb=%lld nbelow=%lld",
                           &r.k, &r.W0, &r.WF, &r.EPS, &r.ninit, &r.nb, &r.lo, &r.hi, r.build, r.mut, r.smain, r.stight, &r.flt,
                           &r.scored, &r.narb, &r.nbelow);
            if (n != 16) { fprintf(stderr, "bad SHARD line in %s: %s", argv[a], line); return 1; }
            S[ns++] = r;
        }
        fclose(f);
    }
    if (!ns) { fprintf(stderr, "no SHARD lines\n"); return 1; }
    for (int s = 1; s < ns; s++)                 /* identical run parameters, build and mutation flags */
        if (S[s].k != S[0].k || S[s].W0 != S[0].W0 || S[s].WF != S[0].WF || S[s].EPS != S[0].EPS || S[s].ninit != S[0].ninit ||
            S[s].nb != S[0].nb || strcmp(S[s].build, S[0].build) || strcmp(S[s].mut, S[0].mut)) {
            fprintf(stderr, "combine: shard %d has different parameters/build/mutation flags than shard 0\n", s); return 1; }
    if (strcmp(S[0].mut, "none")) printf("WARNING: shards were run with CHK_MUTATE=%s (negative control, not a certificate)\n", S[0].mut);
    for (int s = 1; s < ns; s++) {               /* sort by lo, then require disjoint ranges */
        ShardRec r = S[s]; int t = s - 1;
        while (t >= 0 && S[t].lo > r.lo) { S[t + 1] = S[t]; t--; }
        S[t + 1] = r;
    }
    long long covered = 0;
    for (int s = 0; s < ns; s++) {
        if (S[s].lo < 0 || S[s].hi > S[s].nb || S[s].lo >= S[s].hi) { fprintf(stderr, "combine: bad range [%lld,%lld)\n", S[s].lo, S[s].hi); return 1; }
        if (s && S[s].lo < S[s - 1].hi) { fprintf(stderr, "combine: OVERLAPPING shards [%lld,%lld) and [%lld,%lld): refused\n",
                                                  S[s - 1].lo, S[s - 1].hi, S[s].lo, S[s].hi); return 1; }
        covered += S[s].hi - S[s].lo;
    }
    k = S[0].k; m = 2 * k - 3;
    fmpz_t tot, tt, x; fmpz_init(tot); fmpz_init(tt); fmpz_init(x);
    double flt = 0; long long scored = 0, narb = 0, nbelow = 0;
    for (int s = 0; s < ns; s++) {
        if (fmpz_set_str(x, S[s].smain, 10)) { fprintf(stderr, "combine: bad integer\n"); return 1; }
        fmpz_add(tot, tot, x);
        if (fmpz_set_str(x, S[s].stight, 10)) { fprintf(stderr, "combine: bad integer\n"); return 1; }
        fmpz_add(tt, tt, x);
        flt += S[s].flt; scored += S[s].scored; narb += S[s].narb; nbelow += S[s].nbelow;
    }
    arb_t P, C, D; arb_init(P); arb_init(C); arb_init(D);
    prefactor(P, RPREC);
    arb_set_fmpz(C, tot); arb_set_ui(D, 10); arb_pow_ui(D, D, 30, RPREC); arb_div(C, C, D, RPREC); arb_mul(C, C, P, RPREC);
    double pref = arf_get_d(arb_midref(P), ARF_RND_NEAR);
    printf("combine: %d shards, initial boxes covered %lld of %lld%s; scored leaves %lld, arb-evaluated %lld, below 0.999 float %lld\n",
           ns, covered, S[0].nb, covered == S[0].nb ? " (complete)" : " (PARTIAL: still a valid lower bound)", scored, narb, nbelow);
    printf("float total (sum of float leaf values x pref) = %.9f\n", pref * flt);
    print_lower("CERTIFIED  C_k >=", C);
    arb_set_fmpz(C, tt); arb_div(C, C, D, RPREC); arb_mul(C, C, P, RPREC);
    print_lower("certified, tighter valid 3b variant (extra info) C_k >=", C);
    return 0;
}
static void print_floor1e30(char *buf, size_t n, const arb_t x) {   /* floor(1e30 * lower endpoint) as a decimal integer */
    arb_t y, D; arf_t lo; fmpz_t z; arb_init(y); arb_init(D); arf_init(lo); fmpz_init(z);
    arb_set_ui(D, 10); arb_pow_ui(D, D, 30, RPREC); arb_mul(y, x, D, RPREC);
    arb_get_lbound_arf(lo, y, RPREC); arf_get_fmpz(z, lo, ARF_RND_FLOOR);
    char *str = fmpz_get_str(NULL, 10, z); snprintf(buf, n, "%s", str); flint_free(str);
    arb_clear(y); arb_clear(D); arf_clear(lo); fmpz_clear(z);
}

/* PASS1 (an addition, not part of the checker of the paper): per-initial-box records for the Lean shard claims */
static void print_floor2exp(char *buf, size_t n, const arb_t x, slong e) {   /* floor(2^e * lower endpoint) */
    arf_t lo; fmpz_t z; arf_init(lo); fmpz_init(z);
    arb_get_lbound_arf(lo, x, RPREC); arf_mul_2exp_si(lo, lo, e); arf_get_fmpz(z, lo, ARF_RND_FLOOR);
    char *str = fmpz_get_str(NULL, 10, z); snprintf(buf, n, "%s", str); flint_free(str);
    arf_clear(lo); fmpz_clear(z);
}
static void racc_merge(RAcc *rt, const RAcc *ra) {   /* the same merge as the per-thread merge in main() */
    arb_add(rt->sum_main, rt->sum_main, ra->sum_main, RPREC); arb_add(rt->sum_tight, rt->sum_tight, ra->sum_tight, RPREC);
    rt->flt_sum += ra->flt_sum; rt->flt_eval += ra->flt_eval;
    rt->nleaf += ra->nleaf; rt->nskip += ra->nskip; rt->nfast0 += ra->nfast0; rt->narb += ra->narb; rt->nrig0 += ra->nrig0;
    rt->nclassdiff += ra->nclassdiff; rt->nnvdiff += ra->nnvdiff; rt->nbelow += ra->nbelow; rt->nabove += ra->nabove;
    rt->nAdiff += ra->nAdiff; rt->ncentre_bad += ra->ncentre_bad; rt->nenl += ra->nenl; rt->nenl_diff += ra->nenl_diff;
    for (int r = 0; r < NREASON; r++) { rt->reason[r] += ra->reason[r]; rt->reason_flt[r] += ra->reason_flt[r]; rt->reason_rig[r] += ra->reason_rig[r]; }
    if (ra->maxAdiff > rt->maxAdiff) rt->maxAdiff = ra->maxAdiff;
    if (ra->maxEdiff > rt->maxEdiff) rt->maxEdiff = ra->maxEdiff;
    rt->t_arb += ra->t_arb;
}

int main(int argc, char **argv) {
    if (argc >= 2 && strcmp(argv[1], "--selftest") == 0) return selftest(argc, argv);
    if (argc >= 2 && strcmp(argv[1], "--combine") == 0) return combine(argc, argv);
    if (argc >= 4 && strcmp(argv[1], "--count") == 0) {         /* chk_ck14 --count K NINIT: number of initial boxes */
        k = atoi(argv[2]); m = 2 * k - 3;
        Box root; double Rd = k - 2;
        root.lo[0] = 0; root.hi[0] = Rd;
        for (int j = 2; j < k; j++) { root.lo[2 * j - 3] = -Rd; root.hi[2 * j - 3] = Rd; root.lo[2 * j - 2] = (j == 2) ? 0 : -Rd; root.hi[2 * j - 2] = Rd; }
        int nb; Box *bx = initial_boxes(&root, atoi(argv[3]), &nb); free(bx);
        printf("%d\n", nb); return 0;
    }
    if (argc < 5) { fprintf(stderr, "usage: chk_ck14 K W0 WF EPS [--shard LO HI] [--ninit N]   (env: CHK_MUTATE=g+,pref,orderfac,"
                                    "order,noR,class,old3b,flt+,indep,fmaxlo,enl1; CHK_ALL=1; CHK_PROGRESS=1)\n"
                                    "       chk_ck14 --combine FILE...      chk_ck14 --selftest K [N]      chk_ck14 --count K NINIT\n"); return 1; }
    k = atoi(argv[1]); W0 = atof(argv[2]); WF = atof(argv[3]); EPS = atof(argv[4]);
    if (k < 3 || k > 7) { fprintf(stderr, "chk_ck14: need 3 <= K <= 7\n"); return 1; }
    long long ninit = 64LL * omp_get_max_threads(), lo = -1, hi = -1;
    for (int a = 5; a < argc; a++) {
        if (!strcmp(argv[a], "--shard") && a + 2 < argc) { lo = atoll(argv[a + 1]); hi = atoll(argv[a + 2]); a += 2; }
        else if (!strcmp(argv[a], "--ninit") && a + 1 < argc) { ninit = atoll(argv[a + 1]); a += 1; }
        else { fprintf(stderr, "chk_ck14: unknown argument %s\n", argv[a]); return 1; }
    }
    use_q = 0;
    m = 2 * k - 3; s_exp = k - 0.5;
    const char *mu = getenv("CHK_MUTATE");
    if (mu) {
        char buf[256]; snprintf(buf, sizeof buf, "%s", mu);
        for (char *tok = strtok(buf, ","); tok; tok = strtok(NULL, ",")) {
            if (!strcmp(tok, "g+")) mut_g = 1; else if (!strcmp(tok, "pref")) mut_pref = 1;
            else if (!strcmp(tok, "orderfac")) mut_orderfac = 1; else if (!strcmp(tok, "order")) mut_order = 1;
            else if (!strcmp(tok, "noR")) mut_noR = 1; else if (!strcmp(tok, "class")) mut_class = 1;
            else if (!strcmp(tok, "old3b")) mut_old3b = 1; else if (!strcmp(tok, "flt+")) mut_flt = 1;
            else if (!strcmp(tok, "indep")) mut_indep = 1; else if (!strcmp(tok, "fmaxlo")) mut_fmaxlo = 1;
            else if (!strcmp(tok, "enl1")) mut_enl1 = 1;
            else { fprintf(stderr, "unknown CHK_MUTATE token %s\n", tok); return 1; }
        }
        printf("NEGATIVE CONTROL: CHK_MUTATE=%s (g+ %d pref %d orderfac %d order %d noR %d class %d old3b %d flt+ %d indep %d fmaxlo %d enl1 %d)\n", mu, mut_g,
               mut_pref, mut_orderfac, mut_order, mut_noR, mut_class, mut_old3b, mut_flt, mut_indep, mut_fmaxlo, mut_enl1);
    }
    if (getenv("CHK_ALL")) skip_zero_flt = 0;
    if (getenv("CHK_NSTRIP_LOG2")) { nstrip_log2 = atoi(getenv("CHK_NSTRIP_LOG2")); if (nstrip_log2 < 1 || nstrip_log2 > 6) nstrip_log2 = 3; }
    int progress = getenv("CHK_PROGRESS") != NULL;
    double tb = omp_get_wtime();
    build_tables();                       /* box_ck14 float tables (drive the verbatim recursion) */
    { double f = 1; for (int t = 2; t <= k - 2; t++) f *= t; PREF = 2 * M_PI * exp(lgamma(k - 0.5) - lgamma(k + 1.0)) * f; }   /* verbatim */
    own_build_g();                        /* own g table (used for every rigorous leaf value) */
    long long ng = 1LL << rnp, mism = 0;
    for (long long E = 0; E < ng; E++) if (g2own[E] != g2tab[E]) mism++;
    init_proxy_circle();
    double tables_s = omp_get_wtime() - tb;
    /* root box and initial split: verbatim from box_ck14 main() (ninit = 64 * threads unless --ninit is given) */
    Box root; double Rd = k - 2;
    root.lo[0] = 0; root.hi[0] = Rd;
    for (int j = 2; j < k; j++) { root.lo[2 * j - 3] = -Rd; root.hi[2 * j - 3] = Rd; root.lo[2 * j - 2] = (j == 2) ? 0 : -Rd; root.hi[2 * j - 2] = Rd; }
    int nb; Box *boxes = initial_boxes(&root, (int)ninit, &nb);
    if (lo < 0) { lo = 0; hi = nb; }
    if (lo < 0 || hi > nb || lo >= hi) { fprintf(stderr, "chk_ck14: shard range [%lld,%lld) not inside [0,%d)\n", lo, hi, nb); return 1; }
    Acc tot = {0};
    RAcc rt; memset(&rt, 0, sizeof rt); arb_init(rt.sum_main); arb_init(rt.sum_tight);
    long long ndone = 0;
    /* PASS1: per-box records "B t floor(2^257 main) floor(2^257 tight) scored narb arb_s wall_s" (2g units at 2^-256) */
    FILE *boxf = NULL;
    { const char *bp = getenv("CHK_BOXOUT"); if (bp) { boxf = fopen(bp, "w"); if (!boxf) { fprintf(stderr, "cannot open %s\n", bp); return 1; } } }
    double t0 = omp_get_wtime();
    #pragma omp parallel
    {
        Acc acc = {0};
        RAcc ra; memset(&ra, 0, sizeof ra); arb_init(ra.sum_main); arb_init(ra.sum_tight);
        tl_racc = &ra;
        #pragma omp for schedule(dynamic, 1)
        for (long long t = lo; t < hi; t++) {
            /* PASS1: per-box accumulator, recorded, then merged into the thread accumulator */
            RAcc rb; memset(&rb, 0, sizeof rb); arb_init(rb.sum_main); arb_init(rb.sum_tight);
            tl_racc = &rb;
            double tb0 = omp_get_wtime();
            process(&boxes[t], &acc);
            double tb1 = omp_get_wtime();
            if (boxf) {
                char bm[200], bt[200];
                print_floor2exp(bm, sizeof bm, rb.sum_main, 257); print_floor2exp(bt, sizeof bt, rb.sum_tight, 257);
                #pragma omp critical(boxout)
                fprintf(boxf, "B %lld %s %s %lld %lld %.6f %.6f\n", t, bm, bt, rb.nleaf, rb.narb, rb.t_arb, tb1 - tb0);
            }
            racc_merge(&ra, &rb);
            arb_clear(rb.sum_main); arb_clear(rb.sum_tight);
            tl_racc = &ra;
            if (progress) {
                long long dn;
                #pragma omp atomic capture
                dn = ++ndone;
                if (dn % ((hi - lo + 19) / 20) == 0 || dn == hi - lo)
                    fprintf(stderr, "progress: %lld/%lld initial boxes, %.0fs\n", dn, hi - lo, omp_get_wtime() - t0);
            }
        }
        #pragma omp critical
        { tot.lb += acc.lb; tot.mid += acc.mid; tot.extra += acc.extra; tot.voldrop += acc.voldrop; tot.lossdrop += acc.lossdrop; tot.l_int += acc.l_int; tot.l_bnd += acc.l_bnd; tot.l_str += acc.l_str; tot.l_coi += acc.l_coi;
          tot.scored += acc.scored; tot.dropped += acc.dropped; tot.visited += acc.visited;
          arb_add(rt.sum_main, rt.sum_main, ra.sum_main, RPREC); arb_add(rt.sum_tight, rt.sum_tight, ra.sum_tight, RPREC);
          rt.flt_sum += ra.flt_sum; rt.flt_eval += ra.flt_eval;
          rt.nleaf += ra.nleaf; rt.nskip += ra.nskip; rt.nfast0 += ra.nfast0; rt.narb += ra.narb; rt.nrig0 += ra.nrig0;
          rt.nclassdiff += ra.nclassdiff; rt.nnvdiff += ra.nnvdiff; rt.nbelow += ra.nbelow; rt.nabove += ra.nabove;
          rt.nAdiff += ra.nAdiff; rt.ncentre_bad += ra.ncentre_bad; rt.nenl += ra.nenl; rt.nenl_diff += ra.nenl_diff;
          for (int r = 0; r < NREASON; r++) { rt.reason[r] += ra.reason[r]; rt.reason_flt[r] += ra.reason_flt[r]; rt.reason_rig[r] += ra.reason_rig[r]; }
          if (ra.maxAdiff > rt.maxAdiff) rt.maxAdiff = ra.maxAdiff;
          if (ra.maxEdiff > rt.maxEdiff) rt.maxEdiff = ra.maxEdiff;
          rt.t_arb += ra.t_arb; }
        arb_clear(ra.sum_main); arb_clear(ra.sum_tight);
    }
    double wall = omp_get_wtime() - t0;
    if (boxf) fclose(boxf);
    /* float lines: verbatim box_ck14 output format */
    double fact = 1; for (int t = 2; t <= k - 2; t++) fact *= t;
    double pref = 2 * M_PI * exp(lgamma(k - 0.5) - lgamma(k + 1.0)) * fact;
    printf("k=%d W0=%g WF=%g EPS=%g g=%s  C_k lb=%.6f (extra %.6f)  lossdrop(est)=%.6f  scored=%lld dropped=%lld visited=%lld threads=%d wall=%.1fs\n",
           k, W0, WF, EPS, use_q ? "q-D" : "p-D", pref * tot.lb, pref * tot.extra, tot.lossdrop, tot.scored, tot.dropped, tot.visited,
           omp_get_max_threads(), omp_get_wtime() - t0);
    printf("  loss estimates: interior %.6f boundary %.6f straddle %.6f coincident %.6f\n", tot.l_int, tot.l_bnd, tot.l_str, tot.l_coi);
    /* rigorous results */
    arb_t P, C; arb_init(P); arb_init(C);
    prefactor(P, RPREC);
    printf("build %s; initial boxes %d (ninit %lld), this run: [%lld,%lld)%s\n", CHK_BUILD, nb, ninit, lo, hi,
           (lo == 0 && hi == nb) ? " (all)" : " (SHARD: combine with --combine)");
    printf("own g table: %lld edge sets, mismatches vs box_ck14 table: %lld; tables built in %.1fs\n", ng, mism, tables_s);
    printf("prefactor 2 pi Gamma(k-1/2) (k-2)!/k! = "); arb_printn(P, 25, 0); printf("   (float %.17g)\n", pref);
    printf("scored leaves %lld: skipped (float value 0) %lld, rigorous fast zero %lld, arb-evaluated %lld, rigorous value 0: %lld\n",
           rt.nleaf, rt.nskip, rt.nfast0, rt.narb, rt.nrig0);
    printf("float total (sum of float leaf values x pref) = %.9f   [arb-evaluated leaves: %.9f]\n", pref * rt.flt_sum, pref * rt.flt_eval);
    arb_mul(C, P, rt.sum_main, RPREC);
    print_lower("CERTIFIED  C_k >=", C);
    printf("   ratio certified/float = %.6f\n", arf_get_d(arb_midref(C), ARF_RND_NEAR) / (pref * rt.flt_sum));
    arb_mul(C, P, rt.sum_tight, RPREC);
    print_lower("certified, tighter valid 3b variant (extra info: max with the expansion at A + Er) C_k >=", C);
    printf("leaves with rigorous < 0.999 float: %lld   (rigorous > 1.001 float: %lld)\n", rt.nbelow, rt.nabove);
    for (int r = 0; r < NREASON; r++) if (rt.reason[r])
        printf("   %-34s %10lld leaves, float mass %.3e, rigorous mass %.3e (x pref)\n", reason_name[r], rt.reason[r],
               pref * rt.reason_flt[r], pref * rt.reason_rig[r]);
    printf("diagnostics: edge-class/g differences vs float %lld, vertex-count differences %lld, |A_arb - A_float| > 1e-9: %lld "
           "(max %.2e), max |Er_arb - Er_float| %.2e, non-exact centres/widths %lld; 3e (d^- = 0) leaves %lld, 3e decision differences %lld\n",
           rt.nclassdiff, rt.nnvdiff, rt.nAdiff, rt.maxAdiff, rt.maxEdiff, rt.ncentre_bad, rt.nenl, rt.nenl_diff);
    printf("timing: wall %.1fs, threads %d, arb thread-seconds %.1f, %.1f us per arb-evaluated leaf, %.2f us per scored leaf (wall*threads)\n",
           wall, omp_get_max_threads(), rt.t_arb, rt.narb ? 1e6 * rt.t_arb / rt.narb : 0.0,
           rt.nleaf ? 1e6 * wall * omp_get_max_threads() / rt.nleaf : 0.0);
    {   /* machine-readable shard record (exact lower bounds of the sums before the prefactor, floor(1e30 x)) */
        char sm[128], st[128];
        print_floor1e30(sm, sizeof sm, rt.sum_main); print_floor1e30(st, sizeof st, rt.sum_tight);
        printf("SHARD k=%d W0=%.17g WF=%.17g EPS=%.17g ninit=%lld nb=%d lo=%lld hi=%lld build=%s mutate=%s main_floor1e30=%s "
               "tight_floor1e30=%s flt_sum=%.17g scored=%lld narb=%lld nbelow=%lld\n", k, W0, WF, EPS, ninit, nb, lo, hi, CHK_BUILD,
               mu ? mu : "none", sm, st, rt.flt_sum, rt.nleaf, rt.narb, rt.nbelow);
    }
    arb_clear(P); arb_clear(C);
    return 0;
}
