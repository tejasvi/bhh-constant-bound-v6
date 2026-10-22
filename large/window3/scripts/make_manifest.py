#!/usr/bin/env python3
"""Slice manifest for the (60,30,144) claim run (t60) and its instrumented rerun (t60inst).
Inputs (directory DIR): run_t60_<host>.log (building machine's run log: start line with slice S/N and source sha),
slice_<s>.sha (sha256 written by the building machine before upload), t60inst/<host>_<j0>_<j1>/runinst.log (load-time hashes).
Usage: python3 -I make_manifest.py DIR > SLICE_MANIFEST.txt"""
import sys, os, re, glob
D = sys.argv[1]
build = {}
for f in sorted(glob.glob(os.path.join(D, "run_t60_*.log"))):
    host = os.path.basename(f)[len("run_t60_"):-len(".log")]
    t = open(f).read()
    m = re.search(r"start (\S+) t60 grid (\d+) (\d+) (\d+) dtl (\d+) T (\d+) kmax (\d+) slice (\d+)/(\d+) j (\d+)-(\d+) src (\w+)", t)
    if not m:
        sys.exit(f"cannot parse {f}")
    s = int(m.group(8)); build[s] = dict(host=host, time=m.group(1), n=int(m.group(9)), grid=m.group(2, 3, 4), src=m.group(12),
                                       j=(int(m.group(10)), int(m.group(11))))
up = {}
for f in glob.glob(os.path.join(D, "slice_*.sha")):
    s = int(re.search(r"slice_(\d+)\.sha", f).group(1)); up[s] = open(f).read().split()[0]
loads = {}
for f in sorted(glob.glob(os.path.join(D, "t60inst", "*", "runinst.log"))):
    run = os.path.basename(os.path.dirname(f))
    for line in open(f):
        m = re.match(r"slice (\d+) loaded_sha256 (\w+) upload_sha256 (\w+) (MATCH|MISMATCH)", line)
        if m:
            loads.setdefault(int(m.group(1)), []).append((run, m.group(2), m.group(4)))
N = len(build)
print("# slice manifest, (60,30,144) claim tables (triple-table slices s of n = %d; W3SLICE/W3SAVE of the claim source)" % N)
print("# columns: s  n  grid  source_sha16  building_host  build_start_utc  sha256_at_upload  loads_verified(MATCH/total)")
bad = 0
for s in range(N):
    b = build[s]; L = loads.get(s, [])
    nm = sum(1 for _, h, st in L if st == "MATCH" and h == up[s])
    if nm != len(L) or s not in up:
        bad += 1
    print(f"{s:2d} {b['n']} {'/'.join(b['grid'])} {b['src']} {b['host']} {b['time']} {up.get(s, 'MISSING')} {nm}/{len(L)}")
print("# load-time verification: every instrumented machine recomputed sha256 of all %d slices before loading them" % N)
print("# runs:", " ".join(sorted({r for L in loads.values() for r, _, _ in L})))
print("# result: %s" % ("ALL LOADS MATCH THE UPLOAD HASHES" if bad == 0 else f"{bad} slices with mismatches or missing data"))
