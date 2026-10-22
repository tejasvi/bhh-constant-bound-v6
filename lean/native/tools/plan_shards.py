"""Plan the Lean N shards from the pass-1 per-box records (tools/chk_box.c with CHK_BOXOUT).

usage: plan_shards.py P1DIR OUTDIR [--cap ARB_SECONDS] [--group G] [--only K]

Box records (files k{K}_*.box anywhere under P1DIR): "B t main tight scored narb arb_s wall_s", main/tight =
floor(2^257 x lower endpoint) of the C checker's per-box sums in g units, i.e. Lean units (2g at scale 2^-256).
Checks: every box 0..nb-1 exactly once per k; per-k sums vs the frozen SHARD main_floor1e30 totals.
Shards: maximal runs of boxes with main = 0 are FREE (0 <= shardN by shardSum_nonneg) when their C time is >= 1 s;
the other boxes are cut into contiguous shards with sum(arb_s) <= cap (default 90 s, i.e. ~15 min of Lean at 10x).
Claim per shard: v = floor(sum(main) * (1 - 1e-9)) - 1 (Lean can be ~1.5e-12 below C main on single boxes).  Writes OUTDIR/plan_k{K}.tsv and the Lean sources
OUTDIR/BHHShard/K{K}/S{nnnnn}.lean (one native_decide theorem each), G{ggg}.lean (chains of <= G items) and
OUTDIR/BHHShard/K{K}/All.lean (the chain of the groups: S_K <= shardN K 0 2^R).
"""
import os, sys, glob, argparse
from fractions import Fraction

NB = {3: 4096, 4: 262144, 5: 4194304}
RN = {3: 12, 4: 18, 5: 22}
FROZEN = {3: 8414029895173773583018389308, 4: 3661115728433305627352415258, 5: 931381966485951962166491708}

def read_boxes(p1dir, k):
    main = {}; tight = {}; arb = {}; scored = {}
    files = sorted(glob.glob(os.path.join(p1dir, "**", f"k{k}_*.box"), recursive=True))
    for f in files:
        for line in open(f):
            p = line.split()
            if len(p) != 8 or p[0] != "B" or not line.endswith("\n"):
                continue
            t = int(p[1])
            if t in main:
                if main[t] != int(p[2]):
                    raise SystemExit(f"k={k} box {t}: two different records")
                continue
            main[t] = int(p[2]); tight[t] = int(p[3]); scored[t] = int(p[4]); arb[t] = float(p[6])
    return files, main, tight, arb, scored

def plan(k, main, arb, cap, excl=(), lo=0, hi=None):
    nb = NB[k] if hi is None else hi
    def ex(t):
        return any(a <= t < b for a, b in excl)
    seg = []                       # (a, b, kind) kind: 'z' zero run, 'n' nonzero run, 'g' excluded gap
    t = lo
    while t < nb:
        if ex(t):
            u = t
            while u < nb and ex(u):
                u += 1
            seg.append([t, u, 'g']); t = u; continue
        z = main[t] == 0
        u = t
        while u < nb and not ex(u) and (main[u] == 0) == z:
            u += 1
        seg.append([t, u, 'z' if z else 'n'])
        t = u
    # zero runs with little C time are merged into the neighbouring nonzero run
    merged = []
    for a, b, kind in seg:
        if kind == 'z' and sum(arb[x] for x in range(a, b)) < 1.0 and merged and merged[-1][2] == 'n':
            merged[-1][1] = b
        elif kind == 'n' and merged and merged[-1][2] == 'n':
            merged[-1][1] = b
        elif kind == 'z' and merged and merged[-1][2] == 'z':
            merged[-1][1] = b
        else:
            merged.append([a, b, kind])
    items = []                     # (a, b, kind, v, est)
    for a, b, kind in merged:
        if kind == 'g':
            items.append((a, b, 'gap', 0, 0.0))
            continue
        if kind == 'z':
            items.append((a, b, 'free', 0, sum(arb[x] for x in range(a, b))))
            continue
        s = a; acc = 0.0; tot = 0
        for x in range(a, b):
            if x > s and acc + arb[x] > cap:
                items.append((s, x, 'shard', tot, acc)); s = x; acc = 0.0; tot = 0
            acc += arb[x]; tot += main[x]
        items.append((s, b, 'shard', tot, acc))
    out = []
    for a, b, kind, tot, est in items:
        if kind == 'gap':
            out.append((a, b, 'gap', 0, 0.0)); continue
        if kind == 'shard':
            v = (tot * (10 ** 9 - 1)) // 10 ** 9 - 1
            if v <= 0:
                kind = 'free'; v = 0
            out.append((a, b, kind, v, est))
        else:
            out.append((a, b, kind, 0, est))
    return out

PD = 8

SEQ = False

def lean_shard(k, n, a, b, v):
    if SEQ:
        return (f"import BHHCert.Shard\n\nnamespace BHH.Shards\n\n"
                f"theorem k{k}_s{n:05d} : ({v} : Int) ≤ BHH.Cert.shardN {k} {a} {b} := by native_decide\n\nend BHH.Shards\n")
    return (f"import BHHCert.TreePar\n\nnamespace BHH.Shards\n\n"
            f"theorem k{k}_s{n:05d} : ({v} : Int) ≤ BHH.Cert.shardNPar {k} {PD} {a} {b} := by native_decide\n\nend BHH.Shards\n")

def chain_proof(k, parts):
    """parts: list of (a, b, v, term) consecutive; returns (V, A, B, proof term text)"""
    a0, b0, v0, t0 = parts[0]
    expr = t0; V = v0; B = b0
    for a, b, v, t in parts[1:]:
        assert a == B
        expr = f"(BHH.shardN_add_le (by decide) (by decide) {expr} {t})"
        V += v; B = b
    return V, a0, B, expr

def write_lean(k, items, outdir, G, first=1):
    d = os.path.join(outdir, "BHHShard", f"K{k}")
    os.makedirs(d, exist_ok=True)
    shard_terms = []
    n = first - 1
    for a, b, kind, v, est in items:
        if kind == 'gap':
            continue
        if kind == 'shard':
            n += 1
            open(os.path.join(d, f"S{n:05d}.lean"), "w").write(lean_shard(k, n, a, b, v))
            term = f"BHH.Shards.k{k}_s{n:05d}" if SEQ else f"(BHH.le_shardN_of_par BHH.Shards.k{k}_s{n:05d})"
            shard_terms.append((a, b, v, term, f"BHHShard.K{k}.S{n:05d}"))
        else:
            shard_terms.append((a, b, 0, f"(BHH.shardN_nonneg {k} {a} {b})", None))
    if any(it[2] == 'gap' for it in items):
        return n - first + 1, 0, None
    groups = []
    for g0 in range(0, len(shard_terms), G):
        part = shard_terms[g0:g0 + G]
        gi = len(groups) + 1
        imports = [m for _, _, _, _, m in part if m]
        V, A, B, expr = chain_proof(k, [(a, b, v, t) for a, b, v, t, _ in part])
        src = "import BHH.ShardChain\n" + "".join(f"import {m}\n" for m in imports)
        src += (f"\nnamespace BHH.Shards\n\ntheorem k{k}_g{gi:04d} : ({V} : Int) ≤ BHH.Cert.shardN {k} {A} {B} :=\n"
                f"  le_trans (le_of_eq (by norm_num)) {expr}\n\nend BHH.Shards\n")
        open(os.path.join(d, f"G{gi:04d}.lean"), "w").write(src)
        groups.append((A, B, V, f"BHH.Shards.k{k}_g{gi:04d}", f"BHHShard.K{k}.G{gi:04d}"))
    V, A, B, expr = chain_proof(k, [(a, b, v, t) for a, b, v, t, _ in groups])
    assert A == 0 and B == NB[k]
    src = "import BHH.ShardChain\n" + "".join(f"import {m}\n" for *_, m in groups)
    src += (f"\nnamespace BHH.Shards\n\ntheorem k{k}_all : ({V} : Int) ≤ BHH.Cert.shardN {k} 0 (2 ^ BHH.Cert.RN {k}) :=\n"
            f"  le_trans (le_of_eq (by norm_num)) {expr}\n\nend BHH.Shards\n")
    open(os.path.join(d, "All.lean"), "w").write(src)
    return n, len(groups), V

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("p1dir"); ap.add_argument("outdir")
    ap.add_argument("--cap", type=float, default=90.0)
    ap.add_argument("--group", type=int, default=100)
    ap.add_argument("--only", type=int, default=0)
    ap.add_argument("--exclude", action="append", default=[], help="A:B box range not planned (gap)")
    ap.add_argument("--range", default=None, help="A:B plan only this box range (shards numbered from --first)")
    ap.add_argument("--first", type=int, default=1)
    ap.add_argument("--seq", action="store_true", help="sequential shardN theorems (no TreePar)")
    args = ap.parse_args()
    excl = [tuple(int(x) for x in e.split(":")) for e in args.exclude]
    global SEQ
    SEQ = args.seq
    rng = tuple(int(x) for x in args.range.split(":")) if args.range else None
    os.makedirs(args.outdir, exist_ok=True)
    for k in (3, 4, 5):
        if args.only and k != args.only:
            continue
        files, main_, tight, arb, scored = read_boxes(args.p1dir, k)
        nb = NB[k]
        def inex(t):
            return any(a <= t < b for a, b in excl) or (rng is not None and not (rng[0] <= t < rng[1]))
        miss = [t for t in range(nb) if t not in main_ and not inex(t)]
        print(f"k={k}: {len(files)} files, {len(main_)} boxes, missing {len(miss)}", flush=True)
        if miss:
            print(f"  first missing: {miss[:10]}"); continue
        S = sum(main_.values()) if not (excl or rng) else sum(v for t, v in main_.items() if not inex(t))
        fz = Fraction(FROZEN[k], 10 ** 30); ours = Fraction(S, 2 ** 257)
        print(f"  sum main/2^257 = {float(ours):.15e}, frozen main_floor1e30/1e30 = {float(fz):.15e}, rel diff {float((ours - fz) / fz):.3e}")
        print(f"  total arb s {sum(arb.values()):.0f}, max box arb s {max(arb.values()):.1f} (box {max(arb, key=arb.get)}), "
              f"scored {sum(scored.values())}")
        if rng:
            items = plan(k, main_, arb, args.cap, excl, rng[0], rng[1])
        else:
            items = plan(k, main_, arb, args.cap, excl)
        tag = f"_{rng[0]}_{rng[1]}" if rng else ""
        with open(os.path.join(args.outdir, f"plan_k{k}{tag}.tsv"), "w") as fh:
            for i, (a, b, kind, v, est) in enumerate(items):
                fh.write(f"{i}\t{a}\t{b}\t{kind}\t{v}\t{est:.3f}\n")
        ns = sum(1 for it in items if it[2] == 'shard')
        est = sorted((it[4] for it in items if it[2] == 'shard'), reverse=True)
        print(f"  items {len(items)}: shards {ns}, free {len(items) - ns}; largest shard est arb s {est[:5]}")
        n, ng, V = write_lean(k, items, args.outdir, args.group, args.first)
        if V is None:
            print(f"  wrote {n} shard modules (gaps present: no groups yet)", flush=True)
            continue
        Sv = Fraction(V, 2 ** 256)
        print(f"  wrote {n} shard modules, {ng} groups; claimed S_{k}/2^256 = {float(Sv):.15e} (2 x main x (1-1e-9) = "
              f"{float(2 * ours * (1 - Fraction(1, 10**9))):.15e})", flush=True)

if __name__ == "__main__":
    main()
