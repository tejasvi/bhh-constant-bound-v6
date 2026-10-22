/-
Track N: the objects named by the shard theorems (fixed parameters of the paper's runs).  The decisions (`ctxN`) only
steer which boxes are scored; soundness rests on `LeafSoundProp k (Lk k)` and `GTabSound k (gtN k)`.
-/
import BHHCert.Tree
import BHHCert.Cand
import BHHCert.TrigTab

namespace BHH.Cert

/-- the g tables (gmin3, gmax3 arrays) for k = 3, 4, 5, as closed constants (computed once) -/
def gtTab3 : Array Int × Array Int := let t := Flt.buildTables 3; (t.2.1, t.2.2.1)
def gtTab4 : Array Int × Array Int := let t := Flt.buildTables 4; (t.2.1, t.2.2.1)
def gtTab5 : Array Int × Array Int := let t := Flt.buildTables 5; (t.2.1, t.2.2.1)

/-- the g tables of the N track (2g values; `gmin` over completions, `gmax` only steers) -/
def gtN (k : Nat) : GTab :=
  let t := match k with
    | 3 => gtTab3
    | 4 => gtTab4
    | 5 => gtTab5
    | _ => let u := Flt.buildTables k; (u.2.1, u.2.2.1)
  ⟨fun i => t.1[i]!, fun i => t.2[i]!⟩

/-- box_ck14's `PREF` as its double bit pattern (decisions only) -/
def prefBitsN (k : Nat) : UInt64 :=
  match k with
  | 3 => 0x3ff645f7c63f2c6b
  | 4 => 0x3ffbd775b7cef784
  | 5 => 0x400d3bd53432ea4e
  | _ => 0x4025ecdfe7262fb9

/-- run parameters (`W0`, `WF`, `EPS` as doubles): k=3 `0.1 0.0002 1e-12`, k=4 `0.4 0.0005 1e-13`, k=5 (C5r) `0.6 0.00025 3e-13` -/
def ctx3 : Flt.Ctx := Flt.mkCtx 3 0.1 0.0002 1e-12 (Float.ofBits (prefBitsN 3))
def ctx4 : Flt.Ctx := Flt.mkCtx 4 0.4 0.0005 1e-13 (Float.ofBits (prefBitsN 4))
def ctx5 : Flt.Ctx := Flt.mkCtx 5 0.6 0.00025 3e-13 (Float.ofBits (prefBitsN 5))

def ctxN (k : Nat) : Flt.Ctx :=
  match k with
  | 3 => ctx3
  | 4 => ctx4
  | _ => ctx5

/-- number of initial-box rounds: `2^RN k` initial boxes (`ninit` 4096, 262144, 4194304) -/
def RN (k : Nat) : Nat :=
  match k with
  | 3 => 12
  | 4 => 18
  | _ => 22

/-- the leaf function of the N track -/
def Lk (k : Nat) (lo hi : List Int) : Int := (leafLB k (gtN k) cosSinTab floatCand floatAsin lo hi).val

/-- the shard sum of the N track over the initial boxes `[a, b)` -/
def shardN (k a b : Nat) : Int := shardSum k (floatDec (ctxN k)) (Lk k) (RN k) a b

end BHH.Cert
