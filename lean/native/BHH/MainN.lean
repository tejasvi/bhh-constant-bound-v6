/-
The native bound, the terms k = 3, 4, 5: `MainBoundsV2`.

Assembly: `mainBoundsV2_of` (BHH/MainV2.lean) applied to module D's leaf soundness `leafSound_N_final`
(BHH/LeafSound/Final.lean) and the shard sums `BHH.Shards.k3_all`, `k4_all`, `k5_all` (BHHShard/K*/All.lean: chains of
the `native_decide` shard theorems over all initial boxes), with the three numerical checks by `norm_num`.
-/
import BHH.MainV2
import BHH.LeafSound.Final
import BHHShard.K3.All
import BHHShard.K4.All
import BHHShard.K5.All

namespace BHH

open BHH.Cert

/-- The native bound for k = 3, 4, 5 (hypotheses: Green's formula and the vertex lemma along a segment). -/
theorem mainBoundsV2_N : MainBoundsV2 :=
  mainBoundsV2_of leafSound_N_final Shards.k3_all Shards.k4_all Shards.k5_all
    (by norm_num [piThreeHalvesLo, OS]) (by norm_num [piThreeHalvesLo, OS]) (by norm_num [piThreeHalvesLo, OS])

end BHH
