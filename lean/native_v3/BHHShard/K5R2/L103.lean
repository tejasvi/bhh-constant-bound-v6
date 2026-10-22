import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l103 : (0 : Int) ≤ BHH.Cert.shardN5r2 1687552 1703936 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1687552 1703936)

end BHH.Shards
