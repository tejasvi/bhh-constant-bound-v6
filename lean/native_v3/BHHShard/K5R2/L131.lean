import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l131 : (0 : Int) ≤ BHH.Cert.shardN5r2 2146304 2162688 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2146304 2162688)

end BHH.Shards
