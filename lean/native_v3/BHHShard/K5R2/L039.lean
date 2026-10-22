import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l039 : (0 : Int) ≤ BHH.Cert.shardN5r2 638976 655360 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 638976 655360)

end BHH.Shards
