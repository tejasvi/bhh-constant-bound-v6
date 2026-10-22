import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l031 : (0 : Int) ≤ BHH.Cert.shardN5r2 507904 524288 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 507904 524288)

end BHH.Shards
