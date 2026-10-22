import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l099 : (0 : Int) ≤ BHH.Cert.shardN5r2 1622016 1638400 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1622016 1638400)

end BHH.Shards
