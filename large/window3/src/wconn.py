# wconn.py -- window-W "connectivity + local degree" automaton for the x-sorted sweep (generic W >= 1).
#
# Lemma (value). Let H be the graph on the sorted points 0..k-1 whose edges are the pairs (a, b) with 1 <= |a - b| <= W that
# are SURELY adjacent (|y_a - y_b| <= 1). H is a subgraph of G_1. Let u = #{v : v has < 2 neighbours in H}. If H is connected,
# then G_1 is connected, every degree-1 vertex of G_1 has < 2 neighbours in H, so n_1(G_1) <= u, and since p(G_1) >= 1,
#   g(G_1) = p - n_1/2 >= 1 - u/2.
# Hence val(H) = 1{H connected} * max(0, 1 - u/2) satisfies 0 <= val(H) <= g(G_1). val is monotone in the edge set of H, so
# uncertain adjacencies may be treated as absent.
#
# Encoded state after step i (points 0..i placed), window = the last min(W, i+1) points, listed newest first:
#   (part, cnt, u)
#   part: canonical component labels of the window points (newest first), using only H-edges among points 0..i;
#         every component of H[0..i] meets the window (otherwise the state is dead and dropped).
#   cnt:  for each window point, the number of H-neighbours seen so far (capped at 2).
#   u:    number of points whose certificate is final and failed (0 or 1; 2 or more -> dead).
# Step i -> i+1 with inputs a[d] = 1{edge (i+1, i+1-d)} for d = 1..W (0 for nonexistent points):
#   add the new point, merge, update counts; the oldest window point (index i+1-W) leaves the window when i+1-W >= 0:
#   its certificate is final (its last partner i+1 has arrived): cnt >= 2 or u += 1; its component must meet the new window.
# Closing after the last point: all window certificates are final; the window must be a single component.
import sys, itertools

def canon(labels):
    m = {}; out = []
    for x in labels:
        if x not in m: m[x] = len(m)
        out.append(m[x])
    return tuple(out)

def start():
    return ((0,), (0,), 0)

def step(state, a, W):
    """a: tuple of W bits, a[d-1] = edge between new point and the window point d positions back (d=1 newest)."""
    part, cnt, u = state
    n = len(part)                     # current window size (<= W)
    a = tuple(a[d] if d < n else 0 for d in range(W))
    # new point label: fresh
    labels = [100] + list(part)       # newest first: new point, then old window points
    cnts = [0] + list(cnt)
    # merge
    lab = list(labels)
    for d in range(1, n + 1):
        if a[d - 1]:
            old, new = lab[d], lab[0]
            lab = [new if x == old else x for x in lab]
            cnts[0] += 1; cnts[d] += 1
    cnts = [min(c, 2) for c in cnts]
    if n + 1 > W:
        # oldest leaves: position n (index n in lab)
        leaving_lab = lab[n]; leaving_cnt = cnts[n]
        rest = lab[:n]
        if leaving_lab not in rest: return None          # its component can never be reconnected
        u2 = u + (0 if leaving_cnt >= 2 else 1)
        if u2 >= 2: return None
        return (canon(rest), tuple(cnts[:n]), u2)
    return (canon(lab), tuple(cnts), u)

def close_value(state, a, W):
    s = step(state, a, W)
    if s is None: return 0.0
    part, cnt, u = s
    if len(set(part)) != 1: return 0.0
    u2 = u + sum(1 for c in cnt if c < 2)
    return max(0.0, 1.0 - 0.5 * u2)

def enumerate_states(W, KMAX=40):
    st0 = start(); layer = {st0}; allst = {st0}
    for i in range(KMAX):
        nxt = set()
        for st in layer:
            for a in itertools.product((0, 1), repeat=W):
                s = step(st, a, W)
                if s is not None: nxt.add(s)
        allst |= nxt
        if nxt == layer: break
        layer = nxt
    return allst, layer

def direct_value(k, AS, W):
    # AS[a][b] == 1 sure edge
    par = list(range(k))
    def f(x):
        while par[x] != x: x = par[x]
        return x
    nb = [0] * k
    for a_ in range(k):
        for b_ in range(a_ + 1, min(k, a_ + W + 1)):
            if AS[a_][b_] == 1:
                par[f(a_)] = f(b_); nb[a_] += 1; nb[b_] += 1
    roots = len(set(f(x) for x in range(k)))
    if roots != 1: return 0.0
    u = sum(1 for x in range(k) if nb[x] < 2)
    return max(0.0, 1.0 - 0.5 * u)

if __name__ == '__main__':
    for W in (1, 2, 3, 4):
        allst, stat = enumerate_states(W)
        print("W=%d: %d states total, %d in the stationary layer" % (W, len(allst), len(stat)))
