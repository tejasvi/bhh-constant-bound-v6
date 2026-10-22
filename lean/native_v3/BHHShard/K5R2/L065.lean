import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l065 : (0 : Int) ≤ BHH.Cert.shardN5r2 1064960 1081344 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1064960 1081344)

end BHH.Shards
