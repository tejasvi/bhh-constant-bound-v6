# non-rigorous probe: where does a finer t-grid help? Uses PHI lines (k j mantissa exponent) at dt = 1/8 and evaluates the
# secant integral (same three candidates) on sub-grids: uniform 1/8, uniform 1/4, and 1/8 on [0,T1] + 1/4 beyond.
import sys, math
from scipy.special import gammainc, gamma
import numpy as np
phi = {}
for line in sys.stdin:
    p = line.split()
    if p[0] != 'PHI': continue
    k, j, m, e = int(p[1]), int(p[2]), float.fromhex(p[3]), int(p[4])
    phi[(k, j)] = math.log(m) + e * math.log(2)
def seg(s, alpha, beta, a, b):
    g = math.pi - beta
    return math.exp(alpha) * g ** (-s) * gamma(s) * (gammainc(s, g * b) - gammainc(s, g * a))
def integral(k, ts):   # ts: increasing grid points (t values) with known psi
    s = k - 0.5; psi = {t: phi[(k, int(round(t * 8)))] for t in ts}
    tot = seg(s, psi[ts[0]], 0, 0, ts[0])
    for i in range(len(ts) - 1):
        a, b = ts[i], ts[i + 1]; best = seg(s, psi[b], 0, a, b)
        if i >= 1:
            sl = (psi[a] - psi[ts[i - 1]]) / (a - ts[i - 1]); al = psi[a] - sl * a
            if sl < math.pi: best = max(best, seg(s, al, sl, a, b))
        if i + 2 < len(ts):
            sl = (psi[ts[i + 2]] - psi[b]) / (ts[i + 2] - b); al = psi[b] - sl * b
            if sl < math.pi: best = max(best, seg(s, al, sl, a, b))
        tot += best
    return 0.5 * tot
K = sorted(set(k for k, _ in phi))
def total(ts): return sum(integral(k, ts) for k in K if k >= 6)
u8 = [j / 8 for j in range(1, 49)]; u4 = [j / 4 for j in range(1, 25)]
print("dt 1/8: %.7e   dt 1/4: %.7e" % (total(u8), total(u4)))
for T1 in (0.5, 1, 1.5, 2, 3, 4):
    ts = [t for t in u8 if t <= T1] + [t for t in u4 if t > T1]
    print("1/8 on [0,%g], 1/4 beyond: %.7e  (%d points)" % (T1, total(ts), len(ts)))
