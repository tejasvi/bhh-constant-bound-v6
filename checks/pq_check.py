"""Check p(G) = q(G) for all connected graphs on k <= 6 labelled vertices (p = minimum path cover, q = Dong-Cao's bound),
and count the graphs with g = p - D > 0 by k."""
import itertools, sys

def components(adj, verts):
    verts = set(verts); seen = set(); cc = 0
    for v in verts:
        if v in seen: continue
        cc += 1; stack = [v]; seen.add(v)
        while stack:
            u = stack.pop()
            for w in adj[u]:
                if w in verts and w not in seen:
                    seen.add(w); stack.append(w)
    return cc

def min_path_cover(adj, n):
    best = n
    for perm in itertools.permutations(range(n)):
        breaks = sum(1 for a, b in zip(perm, perm[1:]) if b not in adj[a])
        if breaks + 1 < best: best = breaks + 1
    return best

def q_of(adj, n):
    n1 = sum(1 for v in range(n) if len(adj[v]) == 1)
    q = max(1, (n1 + 1) // 2)
    for r in range(1, n):
        for S in itertools.combinations(range(n), r):
            rest = [v for v in range(n) if v not in S]
            q = max(q, components(adj, rest) - len(S))
    return q, n1

for n in range(3, int(sys.argv[1]) + 1):
    pairs = list(itertools.combinations(range(n), 2))
    tot = conn = diff = pos = 0
    for mask in range(1 << len(pairs)):
        adj = {v: set() for v in range(n)}
        for t, (a, b) in enumerate(pairs):
            if mask >> t & 1: adj[a].add(b); adj[b].add(a)
        tot += 1
        if components(adj, range(n)) != 1: continue
        conn += 1
        p = min_path_cover(adj, n); q, n1 = q_of(adj, n)
        if p != q: diff += 1
        if 2 * p - n1 > 0: pos += 1
    print(f'k={n}: labelled graphs {tot}, connected {conn}, p != q: {diff}, g = p - n1/2 > 0: {pos}')
