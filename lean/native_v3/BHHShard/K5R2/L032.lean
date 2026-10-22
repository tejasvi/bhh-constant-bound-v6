import BHH.ShardChainR2
import BHHShard.K5R2.S032001
import BHHShard.K5R2.S032002
import BHHShard.K5R2.S032003
import BHHShard.K5R2.S032004

namespace BHH.Shards

theorem k5r2_l032 : (127070084022730330428613139517541038163283291727914616195008425960466908 : Int) ≤ BHH.Cert.shardN5r2 524288 540672 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 524288 527432) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s032001)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s032002)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s032003)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s032004))

end BHH.Shards
