import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l003 : (0 : Int) ≤ BHH.Cert.shardN5r2 49152 65536 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 49152 65536)

end BHH.Shards
