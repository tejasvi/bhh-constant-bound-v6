/-
Track K: the leaf function evaluated by the kernel (`decide +kernel`): kernel g tables (`gtK`, packed Nat literals),
Taylor cos/sin (`cosSin`), exact candidates (`exactCand`, `exactAsin`); no Float anywhere.  The K1 trees use the
decision parameters `3 0.1 0.0005 1e-10` and `4 0.4 0.01 3e-9` with 512 initial boxes (RNK = 9).
-/
import BHHCert.GTabK
import BHHCert.TreeK
import BHHCert.CandK
import BHHCert.Shard

namespace BHH.Cert

/-- the leaf function of track K -/
def LkK (k : Nat) (lo hi : List Int) : Int := (leafLB k (gtK k) cosSin exactCand exactAsin lo hi).val

/-- initial-box rounds of the K1 trees: 512 initial boxes -/
def RNK : Nat := 9

/-- the decision contexts of the K1 trees (untrusted: they only produce the tree codes) -/
def ctxK1_3 : Flt.Ctx := Flt.mkCtx 3 0.1 0.0005 1e-10 (Float.ofBits (prefBitsN 3))
def ctxK1_4 : Flt.Ctx := Flt.mkCtx 4 0.4 0.01 3e-9 (Float.ofBits (prefBitsN 4))

end BHH.Cert
