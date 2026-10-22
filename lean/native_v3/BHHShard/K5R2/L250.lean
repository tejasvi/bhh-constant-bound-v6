import BHH.ShardChainR2
import BHHShard.K5R2.S250001
import BHHShard.K5R2.S250002
import BHHShard.K5R2.S250003
import BHHShard.K5R2.S250004
import BHHShard.K5R2.S250005

namespace BHH.Shards

theorem k5r2_l250 : (252193229193603738337419437173286653911084277053408870062350368487329899 : Int) ≤ BHH.Cert.shardN5r2 4096000 4112384 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 4096000 4106244) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s250001)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s250002)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s250003)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s250004)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s250005))

end BHH.Shards
