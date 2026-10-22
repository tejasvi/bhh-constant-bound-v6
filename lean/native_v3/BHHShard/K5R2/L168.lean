import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l168 : (0 : Int) ≤ BHH.Cert.shardN5r2 2752512 2768896 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2752512 2768896)

end BHH.Shards
