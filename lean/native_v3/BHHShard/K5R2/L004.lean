import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l004 : (0 : Int) ≤ BHH.Cert.shardN5r2 65536 81920 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 65536 81920)

end BHH.Shards
