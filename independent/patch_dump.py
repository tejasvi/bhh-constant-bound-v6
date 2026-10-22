"""patch_dump.py SRC DST: make a dump-only copy of the checker source. After the per-leaf accounting it prints, for
every leaf whose corner hash is 0 mod N (environment CHK_DUMP=N), a line
  LEAF k lo_0 hi_0 ... lo_{m-1} hi_{m-1} lb <certified leaf lower bound> flt <float value> nstr S gmin G gmax H
to stderr. The certified computation is unchanged. Use with leaf_truth.c (a cross-check; not part of the proof)."""
import sys
if len(sys.argv) != 3:
    sys.exit("usage: patch_dump.py SRC DST")
src, dst = sys.argv[1], sys.argv[2]
s = open(src).read()
anchor = "account:;\n"
assert s.count(anchor) == 1
dump = r'''account:;
    {   /* LEAF DUMP: CHK_DUMP=N prints every leaf whose corner hash is 0 mod N */
        static int dumpN = -1;
        if (dumpN < 0) { const char *e = getenv("CHK_DUMP"); dumpN = e ? atoi(e) : 0; }
        if (dumpN > 0) {
            unsigned long long hsh = 1469598103934665603ULL;
            for (int d = 0; d < m; d++) { union { double x; unsigned long long u; } cv; cv.x = b->lo[d]; hsh ^= cv.u; hsh *= 1099511628211ULL; }
            hsh ^= hsh >> 30; hsh *= 0xBF58476D1CE4E5B9ULL; hsh ^= hsh >> 27; hsh *= 0x94D049BB133111EBULL; hsh ^= hsh >> 31;
            if (hsh % (unsigned long long) dumpN == 0) {
                double lbd = arf_get_d(lb_main, ARF_RND_DOWN);
                #pragma omp critical(leafdump)
                {
                    fprintf(stderr, "LEAF %d", k);
                    for (int d = 0; d < m; d++) fprintf(stderr, " %.17g %.17g", b->lo[d], b->hi[d]);
                    fprintf(stderr, " lb %.17g flt %.17g nstr %d gmin %d gmax %d\n", lbd, fi->flt, nstr, gmin, gmax);
                }
            }
        }
    }
'''
s = s.replace(anchor, dump)
open(dst, "w").write(s)
print("patched")
