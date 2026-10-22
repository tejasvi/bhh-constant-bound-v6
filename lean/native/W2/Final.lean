/-
**The window-2 bound** (version 2 of the paper, Section 4): under Green's formula (2.1) and the vertex lemma along segments
(Lemma 3.1 with Remark 3.2 and (2.2)), `Σ_{k=6}^{30} C_k ≥ 0.0026853042`.

Track N: the computational checks (eight recursion shards, the t-integral of the claims, the nondegeneracy of the
tables) are discharged by `native_decide` in `W2Prod`.
-/
import W2.FinalChecks
import W2Prod.S00
import W2Prod.S01
import W2Prod.S02
import W2Prod.S03
import W2Prod.S04
import W2Prod.S05
import W2Prod.S06
import W2Prod.S07
import W2Prod.TInt
import W2Prod.Nondeg

namespace BHH.W2

theorem w2_bound : W2Bound :=
  w2_bound_of_checks
    (claimsChecked_of_shards W2C.prod.shard00 W2C.prod.shard01 W2C.prod.shard02 W2C.prod.shard03
      W2C.prod.shard04 W2C.prod.shard05 W2C.prod.shard06 W2C.prod.shard07)
    W2C.prod.tint W2C.prod.nondeg

end BHH.W2
