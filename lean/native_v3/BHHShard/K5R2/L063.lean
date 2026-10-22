import BHH.ShardChainR2
import BHHShard.K5R2.S063001

namespace BHH.Shards

theorem k5r2_l063 : (162703997072200210402788925705477156549966307641302511227183566694376 : Int) ≤ BHH.Cert.shardN5r2 1032192 1048576 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 1032192 1040466) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s063001))

end BHH.Shards
