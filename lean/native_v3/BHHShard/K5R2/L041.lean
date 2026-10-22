import BHH.ShardChainR2
import BHHShard.K5R2.S041001

namespace BHH.Shards

theorem k5r2_l041 : (4710425642523376517389613126802298183894389273341775131811223319263729 : Int) ≤ BHH.Cert.shardN5r2 671744 688128 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 671744 673858) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s041001))

end BHH.Shards
