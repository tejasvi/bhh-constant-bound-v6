import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l175 : (0 : Int) ≤ BHH.Cert.shardN5r2 2867200 2883584 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2867200 2883584)

end BHH.Shards
