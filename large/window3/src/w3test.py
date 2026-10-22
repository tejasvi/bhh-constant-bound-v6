# w3test.py -- check the encoded window-3 automaton (w3enum.py) against an absolute-index subset automaton
# (a direct port of c6idea/src/mcdec7.c with Wn = WC = 3, intersection over hypotheses for uncertain tests),
# and check ghat <= g = p - n1/2 (p = 1 iff a Hamiltonian path exists; computed by brute force).
# usage: python3 -I w3test.py NCONF SEED
import sys, random, math, itertools
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import w3enum as E

W = 3

def absolute_value(k, AS, cert):
    # AS[a][b] in {1, 0, -1 (uncertain)}; cert[e] from sure adjacencies within distance W.
    cur = {('M', 0, -1, -1)}
    for i in range(0, k - 1):
        nx = i + 1
        ul = [j for j in range(max(nx - W, 0), i + 1) if AS[nx][j] < 0]
        first = True; nxt = set(); vmin = 1e9
        for h in range(1 << len(ul)):
            adjh = {}
            for j in range(max(nx - W, 0), i + 1): adjh[j] = 1 if AS[nx][j] == 1 else 0
            for q, j in enumerate(ul): adjh[j] = (h >> q) & 1
            tmp = set(); vbest = -1.0
            for (mode, e1, ot, mm) in cur:
                succ = []
                if mode == 'M':
                    if adjh.get(i, 0): succ.append(('M', e1, -1, -1))
                    if i >= 1 and e1 == 0 and nx <= W and adjh.get(0, 0): succ.append(('V', -1, i, -1))
                    succ.append(('L', e1, i, nx))
                else:
                    if adjh.get(i, 0):
                        if nx - ot <= W: succ.append((mode, e1, ot, mm))
                        if mode == 'V': succ.append(('M', ot, -1, -1))
                    if nx - ot <= W and adjh.get(ot, 0): succ.append((mode, e1, i, mm))
                for sc in succ:
                    if nx == k - 1:
                        mo, e1n, otn, mmn = sc; gh = -1.0
                        if mo == 'M': gh = 0.5 * (cert[e1n] + cert[k - 1])
                        elif mo == 'V': gh = 0.5 * (cert[k - 1] + cert[otn])
                        elif k - 1 - otn <= W and adjh.get(otn, 0): gh = 0.5 * (cert[e1n] + cert[mmn])
                        vbest = max(vbest, gh)
                    else:
                        tmp.add(sc)
            if nx == k - 1: vmin = min(vmin, vbest)
            elif first: nxt = tmp; first = False
            else: nxt = nxt & tmp
        if nx == k - 1: return vmin
        cur = nxt
        if not cur: return -1.0
    return -1.0

def encoded_value(k, AS):
    st = E.START
    for i in range(0, k - 1):
        nx = i + 1
        N = 1 if AS[nx][i] == 1 else 0
        S = 1 if (i >= 1 and AS[nx][i - 1] == 1) else 0
        T = 1 if (i >= 2 and AS[nx][i - 2] == 1) else 0
        if nx == k - 1:
            return E.close_value(st, i, N, S, T)
        st = E.step(st, i, N, S, T)
        if not st[3]: return -1.0
    return -1.0

def true_g(k, A):
    # p = 1 iff Hamiltonian path exists (brute force over bitmask DP); n1 = # degree-1 vertices; g = p - n1/2 if connected
    deg = [sum(A[a][b] for b in range(k) if b != a) for a in range(k)]
    n1 = sum(1 for d in deg if d == 1)
    # Hamiltonian path DP
    full = (1 << k) - 1
    dp = [0] * (1 << k)
    for v in range(k): dp[1 << v] |= 1 << v
    for m in range(1, full + 1):
        ends = dp[m]
        if not ends: continue
        for v in range(k):
            if not (ends >> v) & 1: continue
            for u in range(k):
                if (m >> u) & 1 or not A[v][u]: continue
                dp[m | (1 << u)] |= 1 << u
    hp = dp[full] != 0
    return (1 - n1 / 2.0) if hp else None

def main():
    n = int(sys.argv[1]); rng = random.Random(int(sys.argv[2]))
    mism = 0; pos = 0; viol = 0
    for it in range(n):
        k = rng.randint(3, 9)
        # sorted points: increments with positive x, random scale so that many adjacencies occur
        sc = rng.choice([0.3, 0.5, 0.7, 1.0])
        xs = [0.0]; ys = [0.0]
        for _ in range(k - 1):
            r = sc * math.sqrt(rng.random()) * 1.6; th = (rng.random() - 0.5) * math.pi
            xs.append(xs[-1] + r * math.cos(th)); ys.append(ys[-1] + r * math.sin(th))
        dl = rng.choice([0.0, 0.0, 0.03, 0.08, 0.2])
        AS = [[0] * k for _ in range(k)]; A = [[0] * k for _ in range(k)]
        for a in range(k):
            for b in range(k):
                if a == b: continue
                d = math.hypot(xs[a] - xs[b], ys[a] - ys[b]); j = abs(a - b)
                A[a][b] = 1 if d <= 1 else 0
                mg = j * dl / 2 if j >= 2 else 0
                AS[a][b] = 1 if d <= 1 - mg else (0 if d > 1 + mg else -1)
        cert = [1 if sum(1 for j in range(k) if j != e and abs(j - e) <= W and AS[e][j] == 1) >= 2 else 0 for e in range(k)]
        va = absolute_value(k, AS, cert)
        ve = encoded_value(k, AS)
        va = max(va, 0.0); ve = max(ve, 0.0)
        if abs(va - ve) > 1e-12:
            mism += 1
            if mism <= 5: print("MISMATCH k=%d abs %g enc %g dl %g" % (k, va, ve, dl))
        if ve > 0:
            pos += 1
            g = true_g(k, A)
            if g is None or ve > g + 1e-12:
                viol += 1
                if viol <= 5: print("VIOLATION k=%d ghat %g g %s" % (k, ve, g))
    print("configs %d positive %d mismatches %d violations %d" % (n, pos, mism, viol))

if __name__ == '__main__':
    main()
