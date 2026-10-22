/* box_ck14.c -- search program (double precision, OpenMP) for lower bounds on the Dong-Cao terms
 *   C_k = 2 pi Gamma(k-1/2) (k-2)!/k! * int_D r2 g(G_1(y)) A(y)^{-(k-1/2)} dx,
 *   D = { r2 >= 0, eta_2 >= 0, xi_2 <= xi_3 <= ... <= xi_{k-1} },  y_0 = 0, y_1 = (r2, 0), y_j = (xi_j, eta_j),
 * with g = p - n_1/2 of the graph that joins points at distance <= 1 (0 if it is disconnected) and A the area of the
 * union of the unit disks.  Points are numbered from 0 here: the paper's y_1, y_2, y_3, ... are y_0, y_1, y_2, ...
 * The root box [0, k-2] x [-(k-2), k-2]^(2k-4) (with eta_2 >= 0) is bisected breadth first at the widest coordinate
 * into at least 64 x (number of threads) initial boxes, and every box is then processed recursively (process()):
 *   - it is dropped if it lies outside the xi order or gmax = 0, and bisected while its widest width exceeds W0;
 *   - otherwise it is scored with the bound of the paper (Section 3) that applies: the enlarged-disk bound if two
 *     centres can coincide, the straddle bound if one pair straddles the xi order, the bound with events of
 *     undetermined edges if gmin < gmax, and the averaged Taylor bound with the vertex remainder otherwise;
 *   - it is bisected again while the estimated loss of its bound exceeds EPS and the relevant width exceeds WF.
 * The program prints the float sum of the leaf bounds times the prefactor and is not part of the proof: the checker
 * chk_ck14.c contains lines 27-399 of this file verbatim and recomputes every leaf bound in ball arithmetic.
 * usage: box_ck14 K W0 WF EPS [gq]   (gq: Dong-Cao's q in place of p; the two agree for k <= 6)
 * (The usage message printed by main() carries the name of an earlier version.)
 *
 *
 *
 */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <omp.h>

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

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: box_ck10 K W0 WF EPS [gq]\n"); return 1; }
    k = atoi(argv[1]); W0 = atof(argv[2]); WF = atof(argv[3]); EPS = atof(argv[4]);
    use_q = (argc > 5 && strcmp(argv[5], "gq") == 0);
    m = 2 * k - 3; s_exp = k - 0.5;
    build_tables();
    { double f = 1; for (int t = 2; t <= k - 2; t++) f *= t; PREF = 2 * M_PI * exp(lgamma(k - 0.5) - lgamma(k + 1.0)) * f; }
    Box root; double Rd = k - 2;
    root.lo[0] = 0; root.hi[0] = Rd;
    for (int j = 2; j < k; j++) { root.lo[2 * j - 3] = -Rd; root.hi[2 * j - 3] = Rd; root.lo[2 * j - 2] = (j == 2) ? 0 : -Rd; root.hi[2 * j - 2] = Rd; }
    int nb; Box *boxes = initial_boxes(&root, 64 * omp_get_max_threads(), &nb);
    Acc tot = {0};
    double t0 = omp_get_wtime();
    #pragma omp parallel
    {
        Acc acc = {0};
        #pragma omp for schedule(dynamic, 1)
        for (int t = 0; t < nb; t++) process(&boxes[t], &acc);
        #pragma omp critical
        { tot.lb += acc.lb; tot.mid += acc.mid; tot.extra += acc.extra; tot.voldrop += acc.voldrop; tot.lossdrop += acc.lossdrop; tot.l_int += acc.l_int; tot.l_bnd += acc.l_bnd; tot.l_str += acc.l_str; tot.l_coi += acc.l_coi;
          tot.scored += acc.scored; tot.dropped += acc.dropped; tot.visited += acc.visited; }
    }
    double fact = 1; for (int t = 2; t <= k - 2; t++) fact *= t;
    double pref = 2 * M_PI * exp(lgamma(k - 0.5) - lgamma(k + 1.0)) * fact;
    printf("k=%d W0=%g WF=%g EPS=%g g=%s  C_k lb=%.6f (extra %.6f)  lossdrop(est)=%.6f  scored=%lld dropped=%lld visited=%lld threads=%d wall=%.1fs\n",
           k, W0, WF, EPS, use_q ? "q-D" : "p-D", pref * tot.lb, pref * tot.extra, tot.lossdrop, tot.scored, tot.dropped, tot.visited,
           omp_get_max_threads(), omp_get_wtime() - t0);
    printf("  loss estimates: interior %.6f boundary %.6f straddle %.6f coincident %.6f\n", tot.l_int, tot.l_bnd, tot.l_str, tot.l_coi);
    return 0;
}
