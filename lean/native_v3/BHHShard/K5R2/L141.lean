import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l141 : (0 : Int) ≤ BHH.Cert.shardN5r2 2310144 2326528 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2310144 2326528)

end BHH.Shards
