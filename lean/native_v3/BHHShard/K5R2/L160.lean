import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l160 : (0 : Int) ≤ BHH.Cert.shardN5r2 2621440 2637824 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2621440 2637824)

end BHH.Shards
