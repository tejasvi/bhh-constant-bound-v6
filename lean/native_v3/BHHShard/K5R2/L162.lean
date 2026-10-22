import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l162 : (0 : Int) ≤ BHH.Cert.shardN5r2 2654208 2670592 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2654208 2670592)

end BHH.Shards
