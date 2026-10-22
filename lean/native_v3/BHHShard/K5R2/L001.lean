import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l001 : (0 : Int) ≤ BHH.Cert.shardN5r2 16384 32768 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 16384 32768)

end BHH.Shards
