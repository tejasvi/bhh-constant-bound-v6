import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l111 : (0 : Int) ≤ BHH.Cert.shardN5r2 1818624 1835008 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1818624 1835008)

end BHH.Shards
