import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l110 : (0 : Int) ≤ BHH.Cert.shardN5r2 1802240 1818624 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1802240 1818624)

end BHH.Shards
