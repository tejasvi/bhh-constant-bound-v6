import BHH.ShardChainR2
import BHHShard.K5R2.S027001

namespace BHH.Shards

theorem k5r2_l027 : (9113775603078050395276378760307903729434461142043473725684487221423324 : Int) ≤ BHH.Cert.shardN5r2 442368 458752 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 442368 454698) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s027001))

end BHH.Shards
