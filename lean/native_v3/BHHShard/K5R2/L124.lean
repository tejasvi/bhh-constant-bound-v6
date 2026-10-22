import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l124 : (0 : Int) ≤ BHH.Cert.shardN5r2 2031616 2048000 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2031616 2048000)

end BHH.Shards
