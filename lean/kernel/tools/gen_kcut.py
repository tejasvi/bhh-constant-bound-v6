"""Emit the kernel-checked sub-box modules from the output of the untrusted cut generator (BHHCert/KCutGen2.lean).
usage: python3 gen_kcut.py KCUT_OUTPUT K M OUT_ROOT [--boxes t1,t2,...] [--mod-leaves N] [--whole-leaves N]
         [--asm-range a,b] [--leaf F] [--rconst R] [--nboxes NB] [--ns NS] [--shard-import MOD] [--noncomp]
The defaults are those of the earlier kernel-only proof K1 (F = LkK, R = RNK, NB = 512, NS = KSub, MOD = BHHCert.ShardK);
the K2 commands (F = LkKf, R = RNK2_3 or RNK2_4, NB = 4096 or 512, NS = KSub2, MOD = BHHCert.ShardK2) are in GEN_PARAMS.txt.
Per cut box t (more than M leaves), in BHH/NS/K{k}/B{t:03d}/:
  Data.lean  chunk lists x0, x1, ... (consecutive external entries, at most M leaves each), xs = [x0, ...],
             the top code `ctop`, the value `V`, and `top : cutOK k (F k) ctop (initBox k R t).1 (initBox k R t).2
             xs.flatten V = true` (no leaf evaluation: cheap);
  S{j}.lean  chunk theorems `s{i} : subOK k (F k) (xs.getD i []) = true` (at most --mod-leaves leaves per module;
             each theorem at most M leaves: kernel memory grows with the size of one declaration), checked one after
             the other (`set_option Elab.async false`);
  Box.lean   `subAll` (every chunk passes; balanced by_cases cover) and `rb (hL) : RangeBound k R t (t + 1) V`.
Boxes with at most M leaves: consecutive runs of at most --whole-leaves leaves in W{a:03d}.lean, `w : V ≤ shardSumK k
  (F k) R a [codes] := by decide +kernel` and `rb (hL) : RangeBound k R a b V`; runs of value 0 get no file (K2 has no W files).
Asm.lean (only when all NB boxes are present): `range (hL) : RangeBound k R 0 (2 ^ R) S` by a balanced tree of
  `RangeBound.add`, and `S` itself. Nothing here is trusted: the kernel re-checks every claim.
"""
import argparse, os, sys

ap = argparse.ArgumentParser()
ap.add_argument('kcut'); ap.add_argument('k', type=int); ap.add_argument('M', type=int); ap.add_argument('out')
ap.add_argument('--boxes', default='')
ap.add_argument('--mod-leaves', type=int, default=600)
ap.add_argument('--whole-leaves', type=int, default=0, help='leaves per whole-box shard (default M)')
ap.add_argument('--asm-range', default='', help='a,b: also write a partial assembly AsmPart_a_b for [a, b)')
ap.add_argument('--leaf', default='LkK', help='leaf function (LkK for K1, LkKf for K2)')
ap.add_argument('--rconst', default='RNK', help='initial-box rounds constant (RNK, RNK2_3, RNK2_4)')
ap.add_argument('--nboxes', type=int, default=512, help='number of initial boxes = 2^rconst')
ap.add_argument('--ns', default='KSub', help='namespace/dir under BHH (KSub for K1, KSub2 for K2)')
ap.add_argument('--shard-import', default='BHHCert.ShardK', help='module defining the leaf function and rconst')
ap.add_argument('--noncomp', action='store_true', help='mark the data defs noncomputable (no compiled code; the kernel needs none)')
args = ap.parse_args()
k, M = args.k, args.M
WL = args.whole_leaves or M
sel = set(int(x) for x in args.boxes.split(',') if x)

# ---- parse kcut output
boxes = {}   # t -> ('cut', V, top, exts) or ('whole', V, leaves, code)
cur = None
for line in open(args.kcut):
    f = line.split()
    if not f:
        continue
    if f[0] == 'WHOLE':
        assert int(f[1]) == k
        boxes[int(f[2])] = ('whole', int(f[3]), int(f[5]), f[6])
    elif f[0] == 'BOX':
        assert int(f[1]) == k
        cur = int(f[2]); boxes[cur] = ['cut', int(f[3]), None, []]
        nExt = int(f[6])
    elif f[0] == 'TOP':
        boxes[cur][2] = f[1]
    elif f[0] == 'EXT':
        boxes[cur][3].append((int(f[1]), f[2], int(f[3]), f[4], f[5]))
for t, b in boxes.items():
    if b[0] == 'cut':
        assert b[2] is not None and len(b[3]) > 0, t

LEAF, RC, NB = args.leaf, args.rconst, args.nboxes
NC = 'noncomputable ' if args.noncomp else ''
NS = 'BHH.%s.K%d' % (args.ns, k)
DIR = os.path.join(args.out, 'BHH', args.ns, 'K%d' % k)

def ext_lit(e):
    v, code, _, lo, hi = e
    return '(%d, %s, [%s], [%s])' % (v, code, lo.replace(',', ', '), hi.replace(',', ', '))

def tree(n, leaf, var='i', ind='  ', hname='c'):
    """balanced by_cases over i ∈ [0, n): leaf(a) proves the goal for i = a"""
    out = []
    def go(lo, hi, ind, depth):
        if hi - lo == 1:
            out.append('%sobtain rfl : %s = %d := by omega\n%s%s\n' % (ind, var, lo, ind, leaf(lo)))
            return
        mid = (lo + hi) // 2
        out.append('%sby_cases %s%d : %s < %d\n' % (ind, hname, depth, var, mid))
        out.append('%s· ' % ind); go(lo, mid, ind + '  ', depth + 1)
        out.append('%s· ' % ind); go(mid, hi, ind + '  ', depth + 1)
    go(0, n, ind, 0)
    txt, i = '', 0
    while i < len(out):
        if out[i].endswith('· '):
            nxt = out[i + 1]
            txt += out[i] + nxt.lstrip(' '); i += 2
        else:
            txt += out[i]; i += 1
    return txt

def range_tree(pieces, ind='  '):
    """balanced RangeBound.add tree over consecutive pieces [(a, b, term)]"""
    def go(lo, hi):
        if hi - lo == 1:
            return pieces[lo][2]
        mid = (lo + hi) // 2
        return ('(RangeBound.add (by norm_num) (by norm_num) (by norm_num) (by decide)\n%s %s\n%s %s)'
                % (ind, go(lo, mid), ind, go(mid, hi)))
    return go(0, len(pieces))

def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'w') as f:
        f.write(text)

mods = []        # module names of the per-piece glue (for Asm)
pieces = []      # (a, b, term, value)
todo = sorted(t for t in boxes if not sel or t in sel)
# ---- cut boxes
for t in todo:
    b = boxes[t]
    if b[0] != 'cut':
        continue
    _, V, top, exts = b
    # chunks: consecutive externals, at most M leaves
    chunks, curc, acc = [], [], 0
    for e in exts:
        if curc and acc + e[2] > M:
            chunks.append(curc); curc, acc = [], 0
        curc.append(e); acc += e[2]
    chunks.append(curc)
    bns = '%s.B%03d' % (NS, t)
    bdir = os.path.join(DIR, 'B%03d' % t)
    data = ['/- track K sub-box data, k = %d, initial box %d: %d external entries in %d chunks (generated by tools/gen_kcut.py) -/\n'
            % (k, t, len(exts), len(chunks)),
            'import BHHCert.TreeCut\nimport %s\n\nset_option Elab.async false\n\nnamespace %s\n\nopen BHH.Cert\n\n' % (args.shard_import, bns)]
    for i, ch in enumerate(chunks):
        data.append('/-- chunk %d (%d leaves) -/\n%sdef x%d : List ExtEntry := [\n  %s]\n\n'
                    % (i, sum(e[2] for e in ch), NC, i, ',\n  '.join(ext_lit(e) for e in ch)))
    # a list literal of more than ~3,600 constants exceeds the default maxRecDepth (K1: boxes 209 and 449 of k = 4)
    data.append(('set_option maxRecDepth 100000 in\n' if len(chunks) > 3600 else '') +
                '/-- the chunks -/\n%sdef xs : List (List ExtEntry) := [%s]\n\n' % (NC, ', '.join('x%d' % i for i in range(len(chunks)))))
    data.append('/-- the top tree (external nodes: code 15) -/\n%sdef ctop : Nat := %s\n\n/-- the value of the box -/\n%sdef V : Int := %d\n\n' % (NC, top, NC, V))
    data.append('set_option maxRecDepth 100000 in\ntheorem top : cutOK %d (%s %d) ctop (initBox %d %s %d).1 (initBox %d %s %d).2 xs.flatten V = true := by\n'
                '  decide +kernel\n\nend %s\n' % (k, LEAF, k, k, RC, t, k, RC, t, bns))
    write(os.path.join(bdir, 'Data.lean'), ''.join(data))
    # chunk modules
    smods, j, i = [], 0, 0
    while i < len(chunks):
        lv, body = 0, []
        while i < len(chunks) and (not body or lv + sum(e[2] for e in chunks[i]) <= args.mod_leaves):
            lv += sum(e[2] for e in chunks[i])
            body.append('theorem s%d : subOK %d (%s %d) (xs.getD %d []) = true := by\n  decide +kernel\n\n' % (i, k, LEAF, k, i))
            i += 1
        write(os.path.join(bdir, 'S%03d.lean' % j),
              '/- track K sub-box checks, k = %d, initial box %d (generated by tools/gen_kcut.py) -/\n'
              'import %s.Data\n\nset_option Elab.async false\n\nnamespace %s\n\nopen BHH.Cert\n\n%send %s\n'
              % (k, t, bns, bns, ''.join(body), bns))
        smods.append('%s.S%03d' % (bns, j)); j += 1
    box = ['/- track K sub-box glue, k = %d, initial box %d (generated by tools/gen_kcut.py) -/\n' % (k, t)]
    box += ['import %s\n' % m for m in smods]
    box.append('import BHH.MainK\n\nnamespace %s\n\nopen BHH.Cert BHH.KC\n\n' % bns)
    box.append('set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\n'
               'theorem subAll : ∀ i < xs.length, subOK %d (%s %d) (xs.getD i []) = true := by\n'
               '  intro i hi\n  have hl : xs.length = %d := rfl\n  rw [hl] at hi\n' % (k, LEAF, k, len(chunks)))
    box.append(tree(len(chunks), lambda a: 'exact s%d' % a))
    box.append('\ntheorem rb (hL : LeafSoundProp %d (%s %d)) : RangeBound %d %s %d %d %d :=\n'
               '  rangeBound_of_cut hL top (extOK_of_chunks xs subAll)\n\nend %s\n' % (k, LEAF, k, k, RC, t, t + 1, V, bns))
    write(os.path.join(bdir, 'Box.lean'), ''.join(box))
    mods.append('%s.Box' % bns)
    pieces.append((t, t + 1, '(%s.rb hL)' % bns, V))
# ---- whole boxes: consecutive runs
runs, run = [], []
for t in todo:
    b = boxes[t]
    if b[0] == 'whole':
        if run and (run[-1][0] != t - 1 or sum(x[2] for x in run) + b[2] > WL):
            runs.append(run); run = []
        run.append((t, b[1], b[2], b[3]))
    else:
        if run:
            runs.append(run); run = []
if run:
    runs.append(run)
for run in runs:
    a, bb = run[0][0], run[-1][0] + 1
    V = sum(x[1] for x in run)
    if V == 0:
        # nothing to check: `RangeBound.zero`
        pieces.append((a, bb, '(RangeBound.zero %d %s %d %d)' % (k, RC, a, bb), 0))
        continue
    wns = '%s.W%03d' % (NS, a)
    write(os.path.join(DIR, 'W%03d.lean' % a),
          '/- track K whole-box shard, k = %d, initial boxes [%d, %d), %d leaves (generated by tools/gen_kcut.py) -/\n'
          'import %s\nimport BHH.MainK\n\nset_option Elab.async false\n\nnamespace %s\n\nopen BHH.Cert BHH.KC\n\n'
          '/-- tree codes of the initial boxes [%d, %d) -/\ndef codes : List Nat := [%s]\n\n'
          'set_option maxRecDepth 100000 in\ntheorem w : (%d : Int) ≤ shardSumK %d (%s %d) %s %d codes := by\n  decide +kernel\n\n'
          'theorem rb (hL : LeafSoundProp %d (%s %d)) : RangeBound %d %s %d %d %d :=\n'
          '  rangeBound_of_le_shardSumK (by norm_num) hL codes (by decide) w\n\nend %s\n'
          % (k, a, bb, sum(x[2] for x in run), args.shard_import, wns, a, bb, ', '.join(x[3] for x in run), V, k, LEAF, k, RC, a, k, LEAF, k, k, RC, a, bb, V, wns))
    mods.append('%s.W%03d' % (NS, a))
    pieces.append((a, bb, '(%s.rb hL)' % wns, V))
pieces.sort()
# ---- assembly (all boxes present and contiguous)
if pieces and pieces[0][0] == 0 and pieces[-1][1] == NB and all(pieces[i][1] == pieces[i + 1][0] for i in range(len(pieces) - 1)):
    S = sum(p[3] for p in pieces)
    asm = ['/- track K, k = %d: all %d initial boxes (generated by tools/gen_kcut.py) -/\n' % (k, NB)]
    asm += ['import %s\n' % m for m in sorted(mods)]
    asm.append('import BHH.MainK\n\nnamespace %s\n\nopen BHH.Cert BHH.KC\n\n' % NS)
    asm.append('/-- the sum over all initial boxes -/\ndef S : Int := %d\n\n' % S)
    asm.append('theorem range (hL : LeafSoundProp %d (%s %d)) : RangeBound %d %s 0 (2 ^ %s) S := by\n'
               '  have h := %s\n  exact h.mono (by norm_num [S])\n\nend %s\n' % (k, LEAF, k, k, RC, RC, range_tree(pieces, '    '), NS))
    write(os.path.join(DIR, 'Asm.lean'), ''.join(asm))
    print('assembly: S =', S)
if args.asm_range:
    ra, rb_ = (int(x) for x in args.asm_range.split(','))
    part = [p for p in pieces if ra <= p[0] and p[1] <= rb_]
    assert part and part[0][0] == ra and part[-1][1] == rb_ and all(part[i][1] == part[i + 1][0] for i in range(len(part) - 1)), 'pieces do not cover the range'
    S = sum(p[3] for p in part)
    used = [m for m in sorted(mods) if any(('.B%03d.' % p[0]) in m or m.endswith('.W%03d' % p[0]) for p in part)]
    asm = ['/- track K, k = %d: partial assembly over the initial boxes [%d, %d) (generated by tools/gen_kcut.py) -/\n' % (k, ra, rb_)]
    asm += ['import %s\n' % m for m in used]
    asm.append('import BHH.MainK\n\nnamespace %s\n\nopen BHH.Cert BHH.KC\n\n' % NS)
    asm.append('theorem range_%d_%d (hL : LeafSoundProp %d (%s %d)) : RangeBound %d %s %d %d %d := by\n'
               '  have h := %s\n  exact h.mono (by norm_num)\n\nend %s\n' % (ra, rb_, k, LEAF, k, k, RC, ra, rb_, S, range_tree(part, '    '), NS))
    write(os.path.join(DIR, 'AsmPart_%d_%d.lean' % (ra, rb_)), ''.join(asm))
    print('partial assembly [%d, %d): S = %d' % (ra, rb_, S))
nchunks = sum(1 for t in todo if boxes[t][0] == 'cut')
print('k=%d M=%d: cut boxes %d, whole runs %d, pieces %d' % (k, M, nchunks, len(runs), len(pieces)))
