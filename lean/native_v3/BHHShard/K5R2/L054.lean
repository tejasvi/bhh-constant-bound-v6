import BHH.ShardChainR2
import BHHShard.K5R2.S054001
import BHHShard.K5R2.S054002
import BHHShard.K5R2.S054003

namespace BHH.Shards

theorem k5r2_l054 : (179398435967609447217545810717007385823308688993400740074221811940473307 : Int) ≤ BHH.Cert.shardN5r2 884736 901120 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 884736 893962) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s054001)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s054002)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s054003))

end BHH.Shards
