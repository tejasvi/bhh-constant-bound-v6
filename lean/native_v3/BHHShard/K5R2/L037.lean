import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l037 : (0 : Int) ≤ BHH.Cert.shardN5r2 606208 622592 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 606208 622592)

end BHH.Shards
