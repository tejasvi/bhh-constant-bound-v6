#!/usr/bin/env python3
"""Summary of critic-r2's comparison-only underflow counters (W3INST logs of the instrumented rerun t60inst).
Reads every DIR/t60inst/*/inst_*.log; each '# after j J: ...' line carries running minima and counts for its run.
Usage: python3 -I inst_summary.py CERT60_DIR > INST_SUMMARY.txt"""
import sys, os, re, glob, math
D = sys.argv[1]
pat = re.compile(r"# after j (\d+): min product (\S+) \(log2 (\S+)\), min kernel (\S+), min entry/max (\S+) \(log2 (\S+)\), "
                 r"subnormal products (\d+), zero products (\d+), subnormal rescaled (\d+), flushed (\d+)")
rows = []; js = set()
for f in sorted(glob.glob(os.path.join(D, "t60inst", "*", "inst_*.log"))):
    run = os.path.basename(os.path.dirname(f)); last = None; nj = 0
    for line in open(f):
        m = pat.match(line)
        if m:
            last = m; nj += 1; js.add(int(m.group(1)))
    if last is None:
        sys.exit(f"no counter lines in {f}")
    rows.append((run, os.path.basename(f), nj, float.fromhex(last.group(2)), float.fromhex(last.group(4)),
                 float.fromhex(last.group(5)), *(int(last.group(i)) for i in (7, 8, 9, 10))))
print("# underflow counters of the instrumented rerun (comparison-only instrumentation, make_inst.py of critic-r2)")
print("# columns: run  log  j_count  log2(min product)  log2(min kernel)  log2(min entry/max)  subnormal_products  zero_products  subnormal_rescaled  flushed")
for r in rows:
    print(f"{r[0]} {r[1]} {r[2]} {math.log2(r[3]):.3f} {math.log2(r[4]):.3f} {math.log2(r[5]):.3f} {r[6]} {r[7]} {r[8]} {r[9]}")
print(f"# t-nodes covered: {len(js)} (j = {min(js)}..{max(js)})")
print(f"# overall: log2(min product) {min(math.log2(r[3]) for r in rows):.3f}, log2(min kernel) {min(math.log2(r[4]) for r in rows):.3f}, "
      f"log2(min entry/max) {min(math.log2(r[5]) for r in rows):.3f}; subnormal products {sum(r[6] for r in rows)}, "
      f"zero products {sum(r[7] for r in rows)}, subnormal rescaled {sum(r[8] for r in rows)}, flushed {sum(r[9] for r in rows)}")
print("# double precision: smallest normal 2^-1022; no product, kernel or rescaled entry came near it" if
      min(math.log2(r[3]) for r in rows) > -1000 and sum(r[6] + r[7] + r[8] + r[9] for r in rows) == 0 else "# ATTENTION: see counts")
