import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l025 : (0 : Int) ≤ BHH.Cert.shardN5r2 409600 425984 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 409600 425984)

end BHH.Shards
