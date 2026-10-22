import BHH.ShardChainR2
import BHHShard.K5R2.S242001
import BHHShard.K5R2.S242002
import BHHShard.K5R2.S242003

namespace BHH.Shards

theorem k5r2_l242 : (81756677276273297098507676437885572591686154012346328601102596113389661 : Int) ≤ BHH.Cert.shardN5r2 3964928 3981312 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 3964928 3976196) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s242001)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s242002)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s242003))

end BHH.Shards
