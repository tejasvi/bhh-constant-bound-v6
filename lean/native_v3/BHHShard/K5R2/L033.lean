import BHH.ShardChainR2
import BHHShard.K5R2.S033001

namespace BHH.Shards

theorem k5r2_l033 : (17771254082886260123009788862771540438091558222401477855708848231982 : Int) ≤ BHH.Cert.shardN5r2 540672 557056 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 540672 544072) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s033001))

end BHH.Shards
