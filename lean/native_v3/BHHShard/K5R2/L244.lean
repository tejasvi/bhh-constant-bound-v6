import BHH.ShardChainR2
import BHHShard.K5R2.G244_00
import BHHShard.K5R2.G244_01

namespace BHH.Shards

theorem k5r2_l244 : (4160359212988457295830516509077973503201943301039348243640089596721098932 : Int) ≤ BHH.Cert.shardN5r2 3997696 4014080 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) BHH.Shards.k5r2_g244_00 BHH.Shards.k5r2_g244_01)

end BHH.Shards
