import BHH.MainN
import W2.Final

/-! The native bound: `MainBoundsV2` (k = 3, 4, 5) with `W2Bound` (6 ≤ k ≤ 30). -/

namespace BHH

theorem betaBoundV2_N : BetaBoundV2 :=
  betaBoundV2_of mainBoundsV2_N W2.w2_bound

theorem bhhBetaBoundV2_N : BHHBetaBoundV2 :=
  bhhBetaBoundV2_of betaBoundV2_N

end BHH
