import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l071 : (0 : Int) ≤ BHH.Cert.shardN5r2 1163264 1179648 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1163264 1179648)

end BHH.Shards
