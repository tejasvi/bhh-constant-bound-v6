/-
Kernel-side leaf function with the faster untrusted candidates (BHHCert/CandFast.lean): `LkKf k` is `LkK k` with
`fastCand` / `fastAsin` in place of `exactCand` / `exactAsin`. Its leaf soundness (BHH/LeafSound/FinalKf.lean) is the
proof of `leafSound_K_final` with the new candidate arguments.
-/
import BHHCert.ShardK
import BHHCert.CandFast

namespace BHH.Cert

/-- the kernel-side leaf function with the fast candidates -/
def LkKf (k : Nat) (lo hi : List Int) : Int := (leafLB k (gtK k) cosSin fastCand fastAsin lo hi).val

end BHH.Cert
