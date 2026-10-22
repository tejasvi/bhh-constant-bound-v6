import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_g126_01 : (0 : Int) ≤ BHH.Cert.shardN5r2 2078720 2080768 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 2078720 2078976) (BHH.shardN5r2_nonneg 2078976 2079232)) (BHH.shardN5r2_nonneg 2079232 2079488)) (BHH.shardN5r2_nonneg 2079488 2079744)) (BHH.shardN5r2_nonneg 2079744 2080000)) (BHH.shardN5r2_nonneg 2080000 2080256)) (BHH.shardN5r2_nonneg 2080256 2080512)) (BHH.shardN5r2_nonneg 2080512 2080768))

end BHH.Shards
