import BHH.ShardChainR2
import BHHShard.K5R2.S048001
import BHHShard.K5R2.S048002
import BHHShard.K5R2.S048003

namespace BHH.Shards

theorem k5r2_l048 : (114225634736348780186070943168570731567051907193094026394971369912957354 : Int) ≤ BHH.Cert.shardN5r2 786432 802816 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 786432 795904) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s048001)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s048002)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s048003))

end BHH.Shards
