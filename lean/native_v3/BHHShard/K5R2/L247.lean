import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l247 : (0 : Int) ≤ BHH.Cert.shardN5r2 4046848 4063232 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 4046848 4063232)

end BHH.Shards
