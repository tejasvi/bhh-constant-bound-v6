import BHH.ShardChainR2
import BHHShard.K5R2.G082_00
import BHHShard.K5R2.G082_01
import BHHShard.K5R2.G082_02

namespace BHH.Shards

theorem k5r2_l082 : (13156120087571628870452009484550693649805978403617674210385844579317854157 : Int) ≤ BHH.Cert.shardN5r2 1343488 1359872 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) BHH.Shards.k5r2_g082_00 BHH.Shards.k5r2_g082_01) BHH.Shards.k5r2_g082_02)

end BHH.Shards
