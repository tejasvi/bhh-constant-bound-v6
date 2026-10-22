import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l072 : (0 : Int) ≤ BHH.Cert.shardN5r2 1179648 1196032 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1179648 1196032)

end BHH.Shards
