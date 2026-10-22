import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l083 : (0 : Int) ≤ BHH.Cert.shardN5r2 1359872 1376256 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1359872 1376256)

end BHH.Shards
