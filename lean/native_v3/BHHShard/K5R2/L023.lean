import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l023 : (0 : Int) ≤ BHH.Cert.shardN5r2 376832 393216 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 376832 393216)

end BHH.Shards
