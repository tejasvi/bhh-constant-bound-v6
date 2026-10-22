import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l179 : (0 : Int) ≤ BHH.Cert.shardN5r2 2932736 2949120 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2932736 2949120)

end BHH.Shards
