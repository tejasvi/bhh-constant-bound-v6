import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l038 : (0 : Int) ≤ BHH.Cert.shardN5r2 622592 638976 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 622592 638976)

end BHH.Shards
