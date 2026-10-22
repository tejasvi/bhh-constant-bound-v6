import BHH.ShardChainR2
import BHHShard.K5R2.S095001

namespace BHH.Shards

theorem k5r2_l095 : (1114321141656099417811603876380883736358953063514948083356318554365 : Int) ≤ BHH.Cert.shardN5r2 1556480 1572864 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 1556480 1560874) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s095001))

end BHH.Shards
