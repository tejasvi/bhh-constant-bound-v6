# level0_arb.py -- rigorous (arb ball arithmetic) evaluation of the LEVEL-0 bound
#   C_k >= (1/2) int_0^inf t^{k-3/2} e^{-pi t} m_H(t)^{k-3} P2_H(t) dt
# (x-sorted monotone Hamiltonian path, window-1 bound A <= pi + sum u(|z_i|), local endpoint certificates).
# Discretisation (all lower bounds):
#   int_a^b r e^{-t u(r)} dr >= w e^{-t U},  w = (b^2-a^2)/2, U >= u(rbar), rbar = r-weighted mean (Jensen: e^{-t u} convex on [0,1])
#   Theta_H(r1, r2) = (pi - arccos c)^2 (clamped), c = (1 - r1^2 - r2^2)/(2 r1 r2), decreasing in r1, r2 -> use cell corner (b_i, b_j)
#   Psi_k(t) = (pi sum_i w_i e^{-t U_i})^{k-3} * sum_ij Th_ij w_i w_j e^{-t (U_i + U_j)}  is a fixed log-convex function of t;
#   t-integral: on [t_j, t_{j+1}] use the best of: Psi(t_{j+1}) (monotone), left / right extended secants of log Psi (convexity),
#   each integrated exactly with the lower incomplete gamma function; [0, t_1]: Psi(t_1); t > T: dropped.
# usage: level0_arb.py N DT T KMAX
import sys
from flint import arb, arb_mat, ctx
ctx.prec = 100
N = int(sys.argv[1]); DT = arb(sys.argv[2]); T = arb(sys.argv[3]); KMAX = int(sys.argv[4])
pi = arb.pi()
def u(r): return pi - (2 * (r / 2).acos() - (r / 2) * (4 - r * r).sqrt())
def up(x): return x.upper()      # exact arb (radius 0)
def lo(x): return x.lower()
w, U, b = [], [], []
for i in range(N):
    a_, b_ = arb(i) / N, arb(i + 1) / N
    w.append((b_ * b_ - a_ * a_) / 2)                       # exact rational (dyadic/N^2) ball, radius ~0
    rb = (arb(2) / 3) * (b_ ** 3 - a_ ** 3) / (b_ * b_ - a_ * a_)
    U.append(up(u(a_)))
    b.append(b_)
w = [lo(x) for x in w]
Th = arb_mat(N, N)
for i in range(N):
    for j in range(i, N):
        c = lo((1 - b[i] * b[i] - b[j] * b[j]) / (2 * b[i] * b[j]))
        if c >= 1: val = lo(pi * pi)
        elif c <= -1: val = arb(0)
        else: val = lo((pi - c.acos()) ** 2)
        Th[i, j] = val; Th[j, i] = val

nT = int(sys.argv[3]) * 0 + int(round(float(sys.argv[3]) / float(sys.argv[2])))
ts = [DT * j for j in range(1, nT + 1)]
wv = arb_mat(N, 1, w)
logPsi = {k: [] for k in range(3, KMAX + 1)}
for t in ts:
    M = arb_mat(N, 1, [w[i] * (-t * U[i]).exp() for i in range(N)])
    P2 = (M.transpose() * (Th * M))[0, 0]
    m = pi * sum((M[i, 0] for i in range(N)), arb(0))
    for k in range(3, KMAX + 1):
        logPsi[k].append((m ** (k - 3) * P2).log())
def seg_int(s, alpha, beta, a, bb):
    # int_a^bb t^{s-1} exp(-pi t + alpha + beta t) dt, beta < pi (exact, lower incomplete gamma)
    g = pi - beta
    ga = (g * a).gamma_lower(s) if a > 0 else arb(0)
    return alpha.exp() * g ** (-s) * ((g * bb).gamma_lower(s) - ga)
res = {}
for k in range(3, KMAX + 1):
    s = arb(k) - arb(1) / 2
    L = logPsi[k]; n = len(L)
    Llo = [x.lower() for x in L]; Lhi = [x.upper() for x in L]
    total = seg_int(s, Llo[0], arb(0), arb(0), ts[0]).lower()          # [0, t_1]: Psi >= Psi(t_1)
    for j in range(n - 1):
        a_, bb = ts[j], ts[j + 1]
        cands = [seg_int(s, Llo[j + 1], arb(0), a_, bb).lower()]          # monotone
        if j >= 1:   # left secant through (t_{j-1}, t_j) extended to the right
            sig = (Llo[j] - Lhi[j - 1]) / DT; sig = sig.lower()
            alpha = (Llo[j] - sig * ts[j]).lower() if True else None
            # line value at t: Llo[j] + sig (t - t_j) = alpha + sig t ; need alpha exact lower: Llo[j] - sig t_j (sig<0 -> -sig t_j >0)
            cands.append(seg_int(s, alpha, sig, a_, bb).lower())
        if j + 2 < n:  # right secant through (t_{j+1}, t_{j+2}) extended to the left
            sig = ((Lhi[j + 2] - Llo[j + 1]) / DT).upper()
            alpha = (Llo[j + 1] - sig * ts[j + 1]).lower()
            cands.append(seg_int(s, alpha, sig, a_, bb).lower())
        total = total + max(cands)
    res[k] = (total / 2).lower()
    print(f"k={k:2d}: C_k >= {res[k].str(10)}", flush=True)
tot6 = sum((res[k] for k in range(6, KMAX + 1)), arb(0)).lower()
print("sum_{k=6..%d} >= %s" % (KMAX, tot6.str(10)))
