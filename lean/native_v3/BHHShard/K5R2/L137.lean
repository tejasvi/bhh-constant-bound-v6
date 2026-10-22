import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l137 : (0 : Int) ≤ BHH.Cert.shardN5r2 2244608 2260992 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2244608 2260992)

end BHH.Shards
