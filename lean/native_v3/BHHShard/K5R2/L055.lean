import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l055 : (0 : Int) ≤ BHH.Cert.shardN5r2 901120 917504 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 901120 917504)

end BHH.Shards
