import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l254 : (0 : Int) ≤ BHH.Cert.shardN5r2 4161536 4177920 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 4161536 4177920)

end BHH.Shards
