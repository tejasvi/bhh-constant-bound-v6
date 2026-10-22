#!/usr/bin/env python3
"""Instrumented copy of the W3 main evaluator (w3_arb.c, block mode) for the underflow question: comparisons only on values the
program already computes; the PHI lines (printed in %a) must equal the uninstrumented run's bit for bit.
Records per (t_j, level): smallest product v*K in the block-mode loop and in level 1->2, subnormal or zero products, the
smallest positive entry / max before the 2^-e rescaling, rescaled entries that are subnormal or flushed, smallest kernel.
Usage: make_inst.py SRC OUT   (each replacement asserted unique)"""
import sys
src, out = sys.argv[1], sys.argv[2]
t = open(src).read()
def sub(old, new):
    global t
    n = t.count(old)
    if n != 1:
        sys.exit(f"{n} matches for {old[:80]!r}")
    t = t.replace(old, new)
sub("#include <math.h>\n", "#include <math.h>\n#include <float.h>\n")
sub("  double tB = omp_get_wtime();\n",
    "  double tB = omp_get_wtime();\n"
    "  FILE *IF = getenv(\"W3INST\") ? fopen(getenv(\"W3INST\"), \"w\") : NULL;   /* AUDIT */\n"
    "  double G_minx = INFINITY, G_ratio = INFINITY, G_minK = INFINITY; long long G_sub = 0, G_zero = 0, G_subsc = 0, G_flush = 0;\n")
# level 1 -> 2 products
sub("          double x = f * K; int D2 = w3_trans[D][N][S][0];\n",
    "          double x = f * K; int D2 = w3_trans[D][N][S][0];\n"
    "          if (x < L2_minx) L2_minx = x; if (x < DBL_MIN) { if (x == 0) L2_zero++; else L2_sub++; }   /* AUDIT */\n")
sub("    memset(F, 0, sizeof(double) * FS);\n    #pragma omp parallel for schedule(dynamic, 4)\n    for (int c2 = 0; c2 < NC; c2++) {\n",
    "    memset(F, 0, sizeof(double) * FS);\n"
    "    double L2_minx = INFINITY; long long L2_sub = 0, L2_zero = 0;   /* AUDIT */\n"
    "    #pragma omp parallel for schedule(dynamic, 4) reduction(min:L2_minx) reduction(+:L2_sub,L2_zero)\n    for (int c2 = 0; c2 < NC; c2++) {\n")
sub("    { double cs = 0; for (int c = 0; c < NC; c++) cs += clos[c]; if (3 <= KMAX) { phim[3 * (NTV + 1) + j] = cs; phie[3 * (NTV + 1) + j] = E; } }\n",
    "    { double cs = 0; for (int c = 0; c < NC; c++) cs += clos[c]; if (3 <= KMAX) { phim[3 * (NTV + 1) + j] = cs; phie[3 * (NTV + 1) + j] = E; } }\n"
    "    if (IF) fprintf(IF, \"%d 2 minprod %a sub %lld zero %lld\\n\", j, L2_minx, L2_sub, L2_zero);   /* AUDIT */\n"
    "    if (L2_minx < G_minx) G_minx = L2_minx; G_sub += L2_sub; G_zero += L2_zero;\n")
# block-mode loop
sub("        #pragma omp parallel\n        {\n          double *Kb = KBUF + (size_t)omp_get_thread_num() * NR * ND;\n",
    "        double B_minx = INFINITY, B_minK = INFINITY; long long B_sub = 0, B_zero = 0;   /* AUDIT */\n"
    "        #pragma omp parallel\n        {\n          double *Kb = KBUF + (size_t)omp_get_thread_num() * NR * ND;\n")
sub("          #pragma omp for schedule(dynamic, 1)\n          for (size_t blk = 0; blk < (size_t)NR * NR * ND; blk++) {\n",
    "          #pragma omp for schedule(dynamic, 1) reduction(min:B_minx, B_minK) reduction(+:B_sub, B_zero)\n          for (size_t blk = 0; blk < (size_t)NR * NR * ND; blk++) {\n")
sub("            for (size_t q = 0; q < (size_t)NR * ND; q++) Kb[q] = al * exp(-t * (double)ap[q]);\n",
    "            for (size_t q = 0; q < (size_t)NR * ND; q++) Kb[q] = al * exp(-t * (double)ap[q]);\n"
    "            for (size_t q = 0; q < (size_t)NR * ND; q++) if (Kb[q] < B_minK) B_minK = Kb[q];   /* AUDIT */\n")
sub("                for (size_t e = 0; e < ne; e++) { int q = lq[e] + shift; double x = lv[e] * (double)Kb[q]; if (Tb[q]) a1 += x; else a0 += x; }\n                int D0 = w3_trans[D][N][S][0], D1 = w3_trans[D][N][S][1];\n                if (D0 >= 0) g[D0] += a0;\n                if (D1 >= 0) g[D1] += a1;\n                cl += a0 * w3_close[D][N][S][0] + a1 * w3_close[D][N][S][1];\n              }\n              double *Gp = G + ((size_t)cc * NC + cb) * W3_NSTATE;\n              for (int D = 0; D < W3_NSTATE; D++) Gp[D] = g[D];\n              int ccm = irc * NT + (NT - 1 - itc), cbm = irb * NT + (NT - 1 - itb);\n              double *Gm = G + ((size_t)ccm * NC + cbm) * W3_NSTATE;\n              for (int D = 0; D < W3_NSTATE; D++) Gm[D] = g[D];\n              CLP[(size_t)cc * NC + cb] = cl; CLP[(size_t)ccm * NC + cbm] = cl;\n",
    "                for (size_t e = 0; e < ne; e++) { int q = lq[e] + shift; double x = lv[e] * (double)Kb[q]; if (Tb[q]) a1 += x; else a0 += x;\n"
    "                  if (x < B_minx) B_minx = x; if (x < DBL_MIN) { if (x == 0) B_zero++; else B_sub++; } }   /* AUDIT */\n"
    "                int D0 = w3_trans[D][N][S][0], D1 = w3_trans[D][N][S][1];\n                if (D0 >= 0) g[D0] += a0;\n                if (D1 >= 0) g[D1] += a1;\n                cl += a0 * w3_close[D][N][S][0] + a1 * w3_close[D][N][S][1];\n              }\n              double *Gp = G + ((size_t)cc * NC + cb) * W3_NSTATE;\n              for (int D = 0; D < W3_NSTATE; D++) Gp[D] = g[D];\n              int ccm = irc * NT + (NT - 1 - itc), cbm = irb * NT + (NT - 1 - itb);\n              double *Gm = G + ((size_t)ccm * NC + cbm) * W3_NSTATE;\n              for (int D = 0; D < W3_NSTATE; D++) Gm[D] = g[D];\n              CLP[(size_t)cc * NC + cb] = cl; CLP[(size_t)ccm * NC + cbm] = cl;\n")
sub("        #pragma omp parallel for schedule(static)\n        for (int cc = 0; cc < NC; cc++) { double cl = 0; for (int cb = 0; cb < NC; cb++) cl += CLP[(size_t)cc * NC + cb]; clos[cc] = cl; }\n",
    "        #pragma omp parallel for schedule(static)\n        for (int cc = 0; cc < NC; cc++) { double cl = 0; for (int cb = 0; cb < NC; cb++) cl += CLP[(size_t)cc * NC + cb]; clos[cc] = cl; }\n"
    "        if (IF) fprintf(IF, \"%d %d minprod %a sub %lld zero %lld minK %a\\n\", j, i, B_minx, B_sub, B_zero, B_minK);   /* AUDIT */\n"
    "        if (B_minx < G_minx) G_minx = B_minx; if (B_minK < G_minK) G_minK = B_minK; G_sub += B_sub; G_zero += B_zero;\n")
# rescaling
sub("      int e = ilogb(mx);\n      #pragma omp parallel for\n      for (size_t q = 0; q < FS; q++) G[q] = ldexp(G[q], -e);\n",
    "      int e = ilogb(mx);\n"
    "      double R_minpos = INFINITY; long long R_subsc = 0, R_flush = 0;   /* AUDIT */\n"
    "      #pragma omp parallel for reduction(min:R_minpos)\n      for (size_t q = 0; q < FS; q++) if (G[q] > 0 && G[q] < R_minpos) R_minpos = G[q];\n"
    "      #pragma omp parallel for reduction(+:R_subsc, R_flush)\n"
    "      for (size_t q = 0; q < FS; q++) { double o = G[q]; G[q] = ldexp(G[q], -e); if (o > 0 && G[q] < DBL_MIN) { if (G[q] == 0) R_flush++; else R_subsc++; } }\n"
    "      if (IF) fprintf(IF, \"%d %d rescale minpos/max %a subnormal %lld flushed %lld\\n\", j, i, R_minpos / mx, R_subsc, R_flush);   /* AUDIT */\n"
    "      if (R_minpos / mx < G_ratio) G_ratio = R_minpos / mx; G_subsc += R_subsc; G_flush += R_flush;\n")
sub("    for (int k = 3; k <= KMAX; k++) printf(\"PHI %d %d %a %d\\n\", k, j, phim[k * (NTV + 1) + j], phie[k * (NTV + 1) + j]);\n",
    "    for (int k = 3; k <= KMAX; k++) printf(\"PHI %d %d %a %d\\n\", k, j, phim[k * (NTV + 1) + j], phie[k * (NTV + 1) + j]);\n"
    "    if (IF) { fprintf(IF, \"# after j %d: min product %a (log2 %.3f), min kernel %a, min entry/max %a (log2 %.3f), subnormal products %lld, zero products %lld, subnormal rescaled %lld, flushed %lld\\n\",\n"
    "                      j, G_minx, log2(G_minx), G_minK, G_ratio, log2(G_ratio), G_sub, G_zero, G_subsc, G_flush); fflush(IF); }   /* AUDIT */\n")
open(out, "w").write(t)
print("instrumented copy written")
