#!/usr/bin/env python3
"""Bitwise comparison of the claim's PHI lines (cert60/phi_*.out) with the instrumented rerun's (cert60/t60inst/*/phi_*.out).
A PHI line is "PHI k j mantissa(%a) exponent"; lines are compared as exact strings per (k, j).
Usage: python3 -I phi_compare.py CERT60_DIR > PHI_COMPARE.txt"""
import sys, os, glob
D = sys.argv[1]
def load(paths):
    d = {}
    for p in paths:
        for line in open(p):
            f = line.split()
            if len(f) == 5 and f[0] == "PHI":
                key = (int(f[1]), int(f[2]))
                if key in d and d[key] != line.strip():
                    sys.exit(f"conflicting duplicate {key} in {p}")
                d[key] = line.strip()
    return d
claim = load(sorted(glob.glob(os.path.join(D, "phi_*.out"))))
inst = load(sorted(glob.glob(os.path.join(D, "t60inst", "*", "phi_*.out"))))
keys = sorted(set(claim) | set(inst))
same = sum(1 for k in keys if k in claim and k in inst and claim[k] == inst[k])
diff = [k for k in keys if k in claim and k in inst and claim[k] != inst[k]]
only_c = [k for k in keys if k in claim and k not in inst]
only_i = [k for k in keys if k in inst and k not in claim]
print(f"# PHI comparison: claim lines {len(claim)}, instrumented lines {len(inst)}")
print(f"# identical (exact string, k and j and %a mantissa and exponent): {same}")
print(f"# different: {len(diff)}; only in claim: {len(only_c)}; only in instrumented: {len(only_i)}")
for k in diff[:20]:
    print("DIFF", k, "| claim:", claim[k], "| inst:", inst[k])
print("# RESULT:", "BIT-IDENTICAL" if (same == len(claim) == len(inst) and not diff) else "NOT IDENTICAL")
