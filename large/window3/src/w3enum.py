# w3enum.py -- window-3 sweep automaton (x-sorted points, <= 2 open ends, the second open end within the last 3 points),
# window-relative encoding with sure counts, as an extension of c6idea/src/w2enum.py (W2.md 2.4).
#
# Inputs at step i -> i+1 (new point nx = i+1): N = a(i+1, i), S = a(i+1, i-1), T = a(i+1, i-2), each 0/1.
# Uncertain adjacencies are passed as 0: every move and every closing candidate needs some adjacency = 1, so the
# successor set and the closing value are monotone in the inputs, and the intersection over hypotheses equals the
# value at "uncertain = 0".
#
# Descriptor (mode, a, b, q):
#   ('M', x, None, None)   one path on {0..i}, open end i, closed end x
#   ('V', None, None, q)   one path on {0..i}, open ends i and ot = q
#   ('L', x, y, q)         two paths covering {0..i}, open ends i and ot = q, closed ends x and y (unordered, sorted)
# Closed-end entries x: 'P0' (= i), 'P1' (= i-1), 'P2' (= i-2), 'O0'/'O1' (index <= i-3; final window-3 certificate).
# Second open end q: 'Q1' (= i-1), 'Q2' (= i-2), 'Q30'/'Q31' (= i-3, with its final certificate; only for V).
# Shared sure counts (capped at 2) of the neighbours within sorted distance 3 seen so far:
#   c2 for y_{i-2} over {i-5, i-4, i-3, i-1, i};  c1 for y_{i-1} over {i-4, i-3, i-2, i};  c0 for y_i over {i-3, i-2, i-1}.
# Certificate of y_j: 1 iff y_j has >= 2 neighbours y_l with 1 <= |l - j| <= 3.
import sys

def cap(x): return min(x, 2)

def shiftx(x, k2):
    # closed-end entry relative to i -> relative to i+1; k2 = final certificate of y_{i-2}
    if x == 'P0': return 'P1'
    if x == 'P1': return 'P2'
    if x == 'P2': return 'O1' if k2 else 'O0'
    return x

def canonL(x, y, q):
    a, b = sorted((x, y))
    return ('L', a, b, q)

def dominated(d, D):
    # d is dominated by d2 if same mode and q-type, and every entry equal except O0 -> O1 (or Q30 -> Q31), at least one strict
    def better_or_equal(a, b):
        if a == b: return (True, False)
        if (a, b) in (('O0', 'O1'), ('Q30', 'Q31')): return (True, True)
        return (False, False)
    for d2 in D:
        if d2 == d or d2[0] != d[0]: continue
        if d[0] == 'L':
            # compare as multisets: try both pairings
            pairs = [((d[1], d2[1]), (d[2], d2[2])), ((d[1], d2[2]), (d[2], d2[1]))]
            if d[3] != d2[3]: continue
            for pr in pairs:
                ok = True; strict = False
                for a, b in pr:
                    o, s = better_or_equal(a, b)
                    if not o: ok = False; break
                    strict |= s
                if ok and strict: return True
        else:
            ok = True; strict = False
            for a, b in ((d[1], d2[1]), (d[3], d2[3])):
                o, s = better_or_equal(a, b)
                if not o: ok = False; break
                strict |= s
            if ok and strict: return True
    return False

def prune(D):
    D = frozenset(d for d in D if not (d[0] == 'L' and d[3] not in ('Q1', 'Q2')))
    return frozenset(d for d in D if not dominated(d, D))

def adj_ot(q, S, T):
    return S if q == 'Q1' else (T if q == 'Q2' else 0)

def moves(d, i, N, S, T, k2, c1, c2):
    """successors of descriptor d at step i -> i+1. k2 = final cert of y_{i-2}; c1, c2 = counts (for V1 closing ot)."""
    mode, x, y, q = d
    out = set()
    if mode == 'M':
        if N: out.add(('M', shiftx(x, k2), None, None))                                  # M1
        if (i == 1 and x == 'P1' and S) or (i == 2 and x == 'P2' and T):
            out.add(('V', None, None, 'Q1'))                                             # M2: q attaches to y_0
        out.add(canonL(shiftx(x, k2), 'P0', 'Q1'))                                       # M3: new path {i+1}
    elif mode == 'V':
        if N:
            if q == 'Q1': out.add(('V', None, None, 'Q2'))                               # extend i, keep ot = i-1
            elif q == 'Q2': out.add(('V', None, None, 'Q31' if k2 else 'Q30'))           # keep ot = i-2 (now i+1-3)
            # V1: extend i, close ot
            if q == 'Q1': out.add(('M', 'P2', None, None))
            elif q == 'Q2': out.add(('M', 'O1' if k2 else 'O0', None, None))
            else: out.add(('M', 'O1' if q == 'Q31' else 'O0', None, None))
        if adj_ot(q, S, T): out.add(('V', None, None, 'Q1'))                             # extend ot
    else:
        if N and q == 'Q1': out.add(canonL(shiftx(x, k2), shiftx(y, k2), 'Q2'))          # extend i, keep ot
        if adj_ot(q, S, T): out.add(canonL(shiftx(x, k2), shiftx(y, k2), 'Q1'))          # extend ot
    return out

def step(state, i, N, S, T):
    c2, c1, c0, D = state
    k2 = (c2 + T) >= 2
    out = set()
    for d in D: out |= moves(d, i, N, S, T, k2, c1, c2)
    return (cap(c1 + S), cap(c0 + N), cap(N + S + T), prune(out))

def close_value(state, i, N, S, T):
    """value after adding the last point y_{i+1} = y_{k-1}; -1 if no accepted structure."""
    c2, c1, c0, D = state
    cert_im2 = (c2 + T) >= 2
    cert_im1 = (c1 + S) >= 2
    cert_i = (c0 + N) >= 2
    cert_last = (N + S + T) >= 2
    def res(x):
        return {'P0': cert_i, 'P1': cert_im1, 'P2': cert_im2, 'O0': 0, 'O1': 1}[x]
    def res_ot(q):
        return {'Q1': cert_im1, 'Q2': cert_im2, 'Q30': 0, 'Q31': 1}[q]
    best = -1.0
    for (mode, x, y, q) in D:
        if mode == 'M':
            if N: best = max(best, 0.5 * (res(x) + cert_last))                           # M1
            if (i == 1 and x == 'P1' and S) or (i == 2 and x == 'P2' and T):
                best = max(best, 0.5 * (cert_last + cert_i))                             # M2: endpoints i and last
        elif mode == 'V':
            if N: best = max(best, 0.5 * (res_ot(q) + cert_last))                        # extend i (V1)
            if adj_ot(q, S, T): best = max(best, 0.5 * (cert_i + cert_last))             # extend ot
        else:
            if N and adj_ot(q, S, T): best = max(best, 0.5 * (res(x) + res(y)))          # TL closure
    return best

START = (0, 0, 0, frozenset([('M', 'P0', None, None)]))

def inputs_for(i):
    if i == 0: return [(N, 0, 0) for N in (0, 1)]
    if i == 1: return [(N, S, 0) for N in (0, 1) for S in (0, 1)]
    return [(N, S, T) for N in (0, 1) for S in (0, 1) for T in (0, 1)]

if __name__ == '__main__':
    KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    layer = {START}; allstates = {START}
    for i in range(0, KMAX - 1):
        nxt = set()
        for st in layer:
            for (N, S, T) in inputs_for(i):
                ns = step(st, i, N, S, T)
                if ns[3]: nxt.add(ns)
        print(f"after step {i+1}: {len(nxt)} states", flush=True)
        allstates |= nxt
        if nxt == layer: print("stationary"); break
        layer = nxt
    print("total distinct:", len(allstates))
    descs = set()
    for s in allstates: descs |= s[3]
    print("descriptors used:", len(descs))
    sizes = {}
    for s in allstates: sizes[len(s[3])] = sizes.get(len(s[3]), 0) + 1
    print("subset sizes:", dict(sorted(sizes.items())))
