import BHH.ShardChainR2
import BHHShard.K5R2.S221001

namespace BHH.Shards

theorem k5r2_l221 : (837309372056957824269203685395753609825863904209436732580413530148964 : Int) ≤ BHH.Cert.shardN5r2 3620864 3637248 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 3620864 3624960) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s221001))

end BHH.Shards
