/-
`W2Bound` from the three computational checks of the production run alone (claims checked by the shards, the
t-integral check, the nondegeneracy check): every proof module is plugged in.
-/
import W2.FinalOf
import W2.TIntSound
import W2.TabT14
import W2.TabPairMean
import W2.TabA
import W2.TabCen
import W2.TabRot
import W2.TSOf

namespace BHH.W2

open W2C

theorem w2_bound_of_checks (hcc : ClaimsChecked prod.grid prod.dtl prod.kmax prod.claims)
    (htint : tintOK prod.dtl prod.T prod.kmax 8 prod.claims 26853042 (10 ^ 10) = true)
    (hnd : nondegOK prod.grid = true) : W2Bound :=
  w2_bound_of TabB.ringSound TabB.angleSound TabB.angleRange TabB.frangeSound TabB.distSound a1Radial a2Union
    a2LeA1 pairMean rotA2 sectorCen TSO.tableSoundOf tIntBound hcc htint hnd

end BHH.W2
