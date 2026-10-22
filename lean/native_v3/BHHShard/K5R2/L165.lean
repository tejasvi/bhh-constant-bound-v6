import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l165 : (0 : Int) ≤ BHH.Cert.shardN5r2 2703360 2719744 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2703360 2719744)

end BHH.Shards
