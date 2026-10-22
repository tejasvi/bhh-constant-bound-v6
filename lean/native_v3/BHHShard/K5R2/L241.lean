import BHH.ShardChainR2
import BHHShard.K5R2.S241001
import BHHShard.K5R2.S241002
import BHHShard.K5R2.S241003
import BHHShard.K5R2.S241004
import BHHShard.K5R2.S241005
import BHHShard.K5R2.S241006
import BHHShard.K5R2.S241007
import BHHShard.K5R2.S241008
import BHHShard.K5R2.S241009
import BHHShard.K5R2.S241010
import BHHShard.K5R2.S241011
import BHHShard.K5R2.S241012
import BHHShard.K5R2.S241013

namespace BHH.Shards

theorem k5r2_l241 : (87416821577136635828250536416196153165209843768737847884124585613153604 : Int) ≤ BHH.Cert.shardN5r2 3948544 3964928 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 3948544 3949568) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s241001)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s241002)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s241003)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s241004)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s241005)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s241006)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s241007)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s241008)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s241009)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s241010)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s241011)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s241012)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s241013))

end BHH.Shards
