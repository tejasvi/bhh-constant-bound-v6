import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l134 : (0 : Int) ≤ BHH.Cert.shardN5r2 2195456 2211840 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2195456 2211840)

end BHH.Shards
