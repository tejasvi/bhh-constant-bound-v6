"""Import closure of Lean modules inside a source tree, with sha256 sums.
usage: closure.py ROOTDIR MODULE [MODULE...] > SUMS
Every module whose file ROOTDIR/<A/B/C>.lean exists is followed; any other import must belong to an external
package (Mathlib, Batteries, ..., or core), else the script stops.  Prints 'sha256  relpath' sorted by path and,
on stderr, the counts per top-level directory."""
import sys, os, re, hashlib, collections

EXTERNAL = ("Mathlib", "Batteries", "Aesop", "Qq", "ProofWidgets", "Plausible", "LeanSearchClient", "ImportGraph",
            "Init", "Std", "Lean", "Lake")
IMP = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.«»]+)")

root = sys.argv[1]
todo = list(sys.argv[2:])
seen = {}
while todo:
    m = todo.pop()
    if m in seen:
        continue
    path = os.path.join(root, *m.split(".")) + ".lean"
    if not os.path.isfile(path):
        if m.split(".")[0] in EXTERNAL:
            seen[m] = None
            continue
        sys.exit("missing source for %s (%s)" % (m, path))
    data = open(path, "rb").read()
    seen[m] = (hashlib.sha256(data).hexdigest(), os.path.relpath(path, root))
    for line in data.decode("utf-8").splitlines():
        g = IMP.match(line)
        if g:
            todo.append(g.group(1))
rows = sorted(v for v in seen.values() if v)
for h, p in sorted(rows, key=lambda r: r[1]):
    print("%s  %s" % (h, p))
c = collections.Counter(p.split("/")[0] if "/" in p else p for _, p in rows)
print(len(rows), "files:", dict(sorted(c.items())), file=sys.stderr)
