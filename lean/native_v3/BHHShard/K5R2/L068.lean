import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l068 : (0 : Int) ≤ BHH.Cert.shardN5r2 1114112 1130496 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1114112 1130496)

end BHH.Shards
