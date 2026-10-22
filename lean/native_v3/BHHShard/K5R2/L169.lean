import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l169 : (0 : Int) ≤ BHH.Cert.shardN5r2 2768896 2785280 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2768896 2785280)

end BHH.Shards
