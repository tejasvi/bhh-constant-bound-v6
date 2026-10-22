/-
Native proof, refined C5 run (k = 5, W0 0.6, WF 0.00025, EPS 1e-13, ninit 4194304).  Only the decisions
change (`EPS`); the leaf function `Lk 5`, the g table and the initial boxes are those of the native proof (BHHCert/Shard.lean).
-/
import BHHCert.Shard
import BHHCert.TreePar

namespace BHH.Cert

/-- run parameters of the refined C5 run (`W0`, `WF`, `EPS` as doubles): `0.6 0.00025 1e-13` -/
def ctx5r2 : Flt.Ctx := Flt.mkCtx 5 0.6 0.00025 1e-13 (Float.ofBits (prefBitsN 5))

/-- the shard sum over the initial boxes `[a, b)` with the decisions of the refined C5 run -/
def shardN5r2 (a b : Nat) : Int := shardSum 5 (floatDec ctx5r2) (Lk 5) (RN 5) a b

/-- the same sum computed with `Task.spawn` (splits above depth `pd` run in parallel) -/
def shardN5r2Par (pd a b : Nat) : Int := shardSumPar 5 (floatDec ctx5r2) (Lk 5) pd (RN 5) a b

end BHH.Cert
