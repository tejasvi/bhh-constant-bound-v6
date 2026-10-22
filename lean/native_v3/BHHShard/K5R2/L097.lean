import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l097 : (0 : Int) ≤ BHH.Cert.shardN5r2 1589248 1605632 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1589248 1605632)

end BHH.Shards
