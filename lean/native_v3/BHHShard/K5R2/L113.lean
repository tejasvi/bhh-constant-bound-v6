import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l113 : (0 : Int) ≤ BHH.Cert.shardN5r2 1851392 1867776 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1851392 1867776)

end BHH.Shards
