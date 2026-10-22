import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l088 : (0 : Int) ≤ BHH.Cert.shardN5r2 1441792 1458176 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1441792 1458176)

end BHH.Shards
