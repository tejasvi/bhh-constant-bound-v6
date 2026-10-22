import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l007 : (0 : Int) ≤ BHH.Cert.shardN5r2 114688 131072 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 114688 131072)

end BHH.Shards
