import BHH.ShardChainR2
import BHHShard.K5R2.S057001

namespace BHH.Shards

theorem k5r2_l057 : (190043947271332605221196873344453413135292221045278663989387914813317 : Int) ≤ BHH.Cert.shardN5r2 933888 950272 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 933888 942338) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s057001))

end BHH.Shards
