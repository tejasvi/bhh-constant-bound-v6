import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l085 : (0 : Int) ≤ BHH.Cert.shardN5r2 1392640 1409024 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1392640 1409024)

end BHH.Shards
