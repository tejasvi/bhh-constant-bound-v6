import BHH.ShardChainR2
import BHHShard.K5R2.G042_00
import BHHShard.K5R2.G042_01
import BHHShard.K5R2.G042_02

namespace BHH.Shards

theorem k5r2_l042 : (6272014325248837194203085295861511360665630391298261620111171935091644253 : Int) ≤ BHH.Cert.shardN5r2 688128 704512 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) BHH.Shards.k5r2_g042_00 BHH.Shards.k5r2_g042_01) BHH.Shards.k5r2_g042_02)

end BHH.Shards
