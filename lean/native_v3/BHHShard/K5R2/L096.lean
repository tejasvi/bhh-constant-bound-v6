import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l096 : (0 : Int) ≤ BHH.Cert.shardN5r2 1572864 1589248 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1572864 1589248)

end BHH.Shards
