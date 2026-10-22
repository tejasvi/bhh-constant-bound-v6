# Native proof of the three C_k bounds of Theorem 1.1: final assembly

`BHH/MainN3.lean`:

    theorem BHH.mainBoundsV3_N : MainBoundsV3 :=
      mainBoundsV3_of leafSound_N_final Shards.k3_all Shards.k4_all Shards.k5r2_all (three norm_num checks)

`MainBoundsV3` (`BHH/StatementW3.lean`): `C_3 ≥ 0.0117130195`, `C_4 ≥ 0.0063707166`, `C_5 ≥ 0.0035280362`, under
`GreenFormula` and `VertexLemmaSeg`. `BHH/BetaN3.lean` also gives, with `W3/Assembly.lean`, `betaBoundV3At_N_of : 0 ≤ w → b ≤ 5/8 + C₃ + C₄ + C₅ + w →
W3BoundAt w → BetaBoundV3At b` (constants as certified), its `BHHBetaBoundV3At` form, and the paper-constant forms
`betaBoundV3_N_of : W3Bound → BetaBoundV3`, `bhhBetaBoundV3_N_of : W3Bound → BHHBetaBoundV3`; the window-3 bound stays a
hypothesis there and is not proved in this tree. `BHH/StatementW3.lean` holds the statements and `W3/Assembly.lean` the assembly lemmas.

## Axioms

`axioms_N3.txt` is the output of `lean BHH/AxN3.lean`. The theorems depend on `propext`, `Classical.choice`, `Quot.sound`
and `native_decide` auxiliary axioms only: 5,667 in all: `BHH.Shards.k3_s*` (62), `k4_s*` (1,142) and `k5r2_s*` (4,457), one per shard, and the
g-table checks `BHH.gtN_nonneg_D3/D4/D5`, `BHH.E.gtN_check_three/four/five`.

## Files

`SHA256SUMS` lists every file except itself and `README.md`. The `.lean` files are the import closure of `BHH/AxN3.lean` plus the root `BHHCert.lean` of
the precompiled library `BHHCert` and the module it adds (`BHHCert/CandK.lean`): 6,084 files (BHH 73, BHHCert 12 + the root, BHHShard 5,997: K3 64, K4 1,155, K5R2 4,778; W3 1). The only external import
is `Mathlib`. `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`: Lean v4.35.0-rc3, Mathlib c55e6e786f49.
`tools/`: the closure check, the kernel replay tool and the C checker used for the claims. The scripts that planned the
shards and checked the per-range sums are not included: the claims are untrusted lower bounds, every shard file is
included, and the chain types force the ranges to be contiguous. The comments and docstrings of some files were edited
after the build (internal labels removed); compiling those modules again gives the same declarations.

## Build

* `C_3`, `C_4`: the shards `BHHShard/K3`, `BHHShard/K4` and their chains are those of the native proof of version 2 of the paper (`lean/native`).
* `C_5`: the decisions of the refined C5 run (`k = 5`, `W0 0.6`, `WF 0.00025`, `EPS 1e-13`, `ninit 4194304`) are the context
  `ctx5r2` of `BHHCert/ShardR2.lean` (a new file; the other BHHCert files are unchanged), with `shardN5r2 a b =
  shardSum 5 (floatDec ctx5r2) (Lk 5) (RN 5) a b`. Every range `[16384 s, 16384 (s+1))` of the checker run was cut into Lean
  shards `BHHShard/K5R2/S*.lean`, `theorem k5r2_s… : (v : Int) ≤ BHH.Cert.shardN5r2Par pd a b := by native_decide`
  (`pd = 8`, or `12` for single heavy boxes), no shard crossing a range. The claims are floor(Σ main × (1 − 10⁻⁹)) − 1 per
  shard (units 2⁻²⁵⁶) from a first pass of the C checker (`tools/chk_box.c`, per-box sums); per range, the per-box sums
  equal the checker run's `main_floor1e30` to 1.3 × 10⁻¹⁷ relative. The shards were compiled with
  `lean -o`, with the native libraries of `BHHCert` (and modules `TreePar`, `ShardR2`) loaded, on up to about 100 machines with 32 to 96 threads each (4,457 shards; the C first pass and the Lean shards took
  about 5 h in all).
* Chains (`BHH/ShardChainR2.lean`: consecutive ranges add up): `BHHShard/K5R2/L{sss}.lean` gives
  `k5r2_l{sss} : (V_s : Int) ≤ shardN5r2 (16384 s) (16384 (s+1))` for each range `s` (through parts `G{sss}_{pp}`
  for the 20 ranges with more than 100 items), `Q0`-`Q3` chain 64 ranges each and `All.lean` gives
  `k5r2_all : (S : Int) ≤ shardN5r2 0 (2 ^ RN 5)` (4,457 shards and 1,613 ranges of boxes with no claim, by
  `shardN5r2_nonneg`); `C5_ge_of_shardN5r2` turns it into `C_5 ≥ 0.0035280362` (relative headroom 2.5 × 10⁻⁸).

## Build route

`lakefile.toml` defines the libraries `BHH` and `BHHCert` only, so `lake build` covers the `BHH` and `BHHCert` modules
(all of them except `BHH/MainN3.lean`, `BHH/BetaN3.lean` and `BHH/AxN3.lean`, which import shard or window-3 modules).
The other modules are compiled with plain `lean -o` (`-R .`, the options of `lakefile.toml` as `-D` flags,
`LEAN_PATH` from `lake env printenv LEAN_PATH`), in this order:
1. the shards `BHHShard/K3/S*`, `BHHShard/K4/S*` and `BHHShard/K5R2/S*`, each with `--load-dynlib` of the native
   libraries that its `native_decide` evaluates (`libBHH_BHHCert.so`, and for the `shardNPar`/`shardN5r2Par` shards also
   the module libraries `BHH_BHHCert_TreePar.so` and, for K5R2, `BHH_BHHCert_ShardR2.so`, all built by `lake build`);
2. the chains: `BHHShard/K3/G*` then `BHHShard/K3/All`; `BHHShard/K4/G*` then `BHHShard/K4/All`; `BHHShard/K5R2/G*`,
   then `L*`, then `Q*`, then `BHHShard/K5R2/All`;
3. `W3/Assembly.lean`, `BHH/MainN3.lean`, `BHH/BetaN3.lean`, and `BHH/AxN3.lean` (which prints `axioms_N3.txt`).

## Kernel replay

`tools/ReplayMods.lean` (`Lean.Kernel.Environment.replay`, as in lean4checker) imports `Mathlib` and sends every constant
of the 6,083 modules of the closure (all but `BHH.AxN3`) to the kernel again: 14,364 constants were checked and none was
rejected or missing (22 s). Skipped by `replay` (unsafe compiler auxiliaries): 15 `*._unsafe_rec` constants.
