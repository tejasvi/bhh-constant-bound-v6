import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l012 : (0 : Int) ≤ BHH.Cert.shardN5r2 196608 212992 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 196608 212992)

end BHH.Shards
