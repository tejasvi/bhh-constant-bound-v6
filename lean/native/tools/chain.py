"""Build the group modules and All.lean for one k from the plan files (main plan with gaps + range plans).
usage: chain.py K OUTDIR PLAN[:FIRST[:seq]] [PLAN[:FIRST[:seq]] ...] [--group G]
Each PLAN is a plan_k*.tsv written by plan_shards.py; FIRST is the number of its first shard module (default 1).
Items of kind 'gap' must be covered exactly by the other plans."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from plan_shards import chain_proof, NB

def main():
    a = sys.argv[1:]
    G = 100
    if "--group" in a:
        i = a.index("--group"); G = int(a[i + 1]); del a[i:i + 2]
    k = int(a[0]); outdir = a[1]; plans = a[2:]
    items = []
    for spec in plans:
        parts = spec.split(":")
        path = parts[0]; first = parts[1] if len(parts) > 1 else "1"; seq = len(parts) > 2 and parts[2] == "seq"
        n = int(first) - 1
        for line in open(path):
            i, x, y, kind, v, est = line.rstrip("\n").split("\t")
            x, y, v = int(x), int(y), int(v)
            if kind == "gap":
                continue
            if kind == "shard":
                n += 1
                t = f"BHH.Shards.k{k}_s{n:05d}" if seq else f"(BHH.le_shardN_of_par BHH.Shards.k{k}_s{n:05d})"
                items.append((x, y, v, t, f"BHHShard.K{k}.S{n:05d}"))
            else:
                items.append((x, y, 0, f"(BHH.shardN_nonneg {k} {x} {y})", None))
    items.sort()
    pos = 0
    for x, y, *_ in items:
        if x != pos:
            raise SystemExit(f"coverage error at box {pos} (next item starts at {x})")
        pos = y
    if pos != NB[k]:
        raise SystemExit(f"coverage ends at {pos}, expected {NB[k]}")
    d = os.path.join(outdir, "BHHShard", f"K{k}")
    os.makedirs(d, exist_ok=True)
    groups = []
    for g0 in range(0, len(items), G):
        part = items[g0:g0 + G]
        gi = len(groups) + 1
        V, A, B, expr = chain_proof(k, [(x, y, v, t) for x, y, v, t, _ in part])
        src = "import BHH.ShardChain\n" + "".join(f"import {m}\n" for *_, m in part if m)
        src += (f"\nnamespace BHH.Shards\n\ntheorem k{k}_g{gi:04d} : ({V} : Int) ≤ BHH.Cert.shardN {k} {A} {B} :=\n"
                f"  le_trans (le_of_eq (by norm_num)) {expr}\n\nend BHH.Shards\n")
        open(os.path.join(d, f"G{gi:04d}.lean"), "w").write(src)
        groups.append((A, B, V, f"BHH.Shards.k{k}_g{gi:04d}", f"BHHShard.K{k}.G{gi:04d}"))
    V, A, B, expr = chain_proof(k, [(x, y, v, t) for x, y, v, t, _ in groups])
    src = "import BHH.ShardChain\n" + "".join(f"import {m}\n" for *_, m in groups)
    src += (f"\nnamespace BHH.Shards\n\ntheorem k{k}_all : ({V} : Int) ≤ BHH.Cert.shardN {k} 0 (2 ^ BHH.Cert.RN {k}) :=\n"
            f"  le_trans (le_of_eq (by norm_num)) {expr}\n\nend BHH.Shards\n")
    open(os.path.join(d, "All.lean"), "w").write(src)
    print(f"k={k}: {len(items)} items, {len(groups)} groups, S = {V}")

if __name__ == "__main__":
    main()
