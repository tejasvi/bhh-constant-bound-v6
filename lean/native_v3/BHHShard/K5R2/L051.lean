import BHH.ShardChainR2
import BHHShard.K5R2.S051001
import BHHShard.K5R2.S051002
import BHHShard.K5R2.S051003
import BHHShard.K5R2.S051004

namespace BHH.Shards

theorem k5r2_l051 : (78720545597294825838485149395117657355396750203337170000129649773524262 : Int) ≤ BHH.Cert.shardN5r2 835584 851968 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 835584 844800) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s051001)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s051002)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s051003)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s051004))

end BHH.Shards
