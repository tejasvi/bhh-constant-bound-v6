import BHH.ShardChainR2
import BHHShard.K5R2.S056001
import BHHShard.K5R2.S056002
import BHHShard.K5R2.S056003
import BHHShard.K5R2.S056004

namespace BHH.Shards

theorem k5r2_l056 : (126416128611791839930523235816900280532605064353835011279995728354274850 : Int) ≤ BHH.Cert.shardN5r2 917504 933888 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 917504 925952) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s056001)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s056002)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s056003)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s056004))

end BHH.Shards
