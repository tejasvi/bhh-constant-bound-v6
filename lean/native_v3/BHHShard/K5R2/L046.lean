import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l046 : (0 : Int) ≤ BHH.Cert.shardN5r2 753664 770048 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 753664 770048)

end BHH.Shards
