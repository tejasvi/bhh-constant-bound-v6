/-
The kernel-only proof, K2: the trees of C_3 at the paper's parameters (`3 0.1 0.0002 1e-12`, 4096 initial boxes, the
native proof's k = 3 tree) and of C_4 for the `4 0.4 0.002 3e-10` tree (512 initial boxes).
The decision contexts are untrusted (they only shape the trees); the leaf function is `LkKf` (BHHCert/ShardKf.lean).
-/
import BHHCert.ShardKf

namespace BHH.Cert

/-- initial-box rounds of the K2 trees: 4096 initial boxes for k = 3, 512 for k = 4 -/
def RNK2_3 : Nat := 12
def RNK2_4 : Nat := 9

/-- the decision contexts of the K2 trees (untrusted) -/
def ctxK2_3 : Flt.Ctx := Flt.mkCtx 3 0.1 0.0002 1e-12 (Float.ofBits (prefBitsN 3))
def ctxK2_4 : Flt.Ctx := Flt.mkCtx 4 0.4 0.002 3e-10 (Float.ofBits (prefBitsN 4))

end BHH.Cert
