import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l104 : (0 : Int) ≤ BHH.Cert.shardN5r2 1703936 1720320 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1703936 1720320)

end BHH.Shards
