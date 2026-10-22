# wconntest.py -- encoded window-W connectivity automaton (wconn.py) vs direct computation, and val <= g (brute force).
import sys, os, random, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wconn as C
import w3test as R          # for true_g
def encoded(k, AS, W):
    st = C.start()
    for i in range(0, k - 1):
        nx = i + 1
        a = tuple(1 if (nx - d >= 0 and AS[nx][nx - d] == 1) else 0 for d in range(1, W + 1))
        if nx == k - 1: return C.close_value(st, a, W)
        st = C.step(st, a, W)
        if st is None: return 0.0
    return 0.0
def main():
    n = int(sys.argv[1]); rng = random.Random(int(sys.argv[2])); W = int(sys.argv[3])
    mism = viol = pos = 0
    for it in range(n):
        k = rng.randint(2, 9); sc = rng.choice([0.3, 0.5, 0.7, 1.0])
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
        ve = encoded(k, AS, W); vd = C.direct_value(k, AS, W)
        if abs(ve - vd) > 1e-12:
            mism += 1
            if mism <= 5: print("MISMATCH k=%d enc %g direct %g" % (k, ve, vd))
        if vd > 0:
            pos += 1
            g = R.true_g(k, A) if k >= 2 else None
            # g for connected non-traceable graphs is p - n1/2 with p >= 2; true_g returns None then: compute lower bound 1 - n1/2
            deg = [sum(A[a][b] for b in range(k) if b != a) for a in range(k)]
            n1 = sum(1 for d in deg if d == 1)
            # connectivity of G_1
            seen = {0}; st = [0]
            while st:
                x = st.pop()
                for y in range(k):
                    if A[x][y] and y not in seen: seen.add(y); st.append(y)
            if len(seen) != k or vd > 1 - n1 / 2 + 1e-12:
                viol += 1
                if viol <= 5: print("VIOLATION k=%d val %g conn %d n1 %d" % (k, vd, len(seen) == k, n1))
    print("W=%d configs %d positive %d mismatches %d violations %d" % (W, n, pos, mism, viol))
main()
