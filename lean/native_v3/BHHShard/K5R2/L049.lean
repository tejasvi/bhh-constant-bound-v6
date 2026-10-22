import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l049 : (0 : Int) ≤ BHH.Cert.shardN5r2 802816 819200 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 802816 819200)

end BHH.Shards
