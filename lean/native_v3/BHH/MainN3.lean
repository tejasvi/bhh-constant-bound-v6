import BHH.MainV3
import BHH.LeafSound.Final
import BHHShard.K3.All
import BHHShard.K4.All
import BHHShard.K5R2.All

/-! Theorem 1.1 of the paper, the terms `k = 3, 4, 5` (native proof): `C_3`, `C_4` from the shards of `shardN 3`, `shardN 4`, `C_5` from
the shards of `shardN5r2` (the refined C5 run). -/

namespace BHH

open BHH.Cert

theorem mainBoundsV3_N : MainBoundsV3 :=
  mainBoundsV3_of leafSound_N_final Shards.k3_all Shards.k4_all Shards.k5r2_all
    (by norm_num [piThreeHalvesLo, OS]) (by norm_num [piThreeHalvesLo, OS]) (by norm_num [piThreeHalvesLo, OS])

end BHH
