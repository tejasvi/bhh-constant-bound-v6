import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l128 : (0 : Int) ≤ BHH.Cert.shardN5r2 2097152 2113536 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2097152 2113536)

end BHH.Shards
