import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l135 : (0 : Int) ≤ BHH.Cert.shardN5r2 2211840 2228224 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2211840 2228224)

end BHH.Shards
