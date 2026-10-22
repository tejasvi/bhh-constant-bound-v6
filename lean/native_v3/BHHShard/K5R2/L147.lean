import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l147 : (0 : Int) ≤ BHH.Cert.shardN5r2 2408448 2424832 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2408448 2424832)

end BHH.Shards
