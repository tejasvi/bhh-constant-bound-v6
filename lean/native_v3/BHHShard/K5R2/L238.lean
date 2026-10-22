import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l238 : (0 : Int) ≤ BHH.Cert.shardN5r2 3899392 3915776 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 3899392 3915776)

end BHH.Shards
