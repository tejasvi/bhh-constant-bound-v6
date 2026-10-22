import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l066 : (0 : Int) ≤ BHH.Cert.shardN5r2 1081344 1097728 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1081344 1097728)

end BHH.Shards
