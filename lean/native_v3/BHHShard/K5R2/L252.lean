import BHH.ShardChainR2
import BHHShard.K5R2.G252_00
import BHHShard.K5R2.G252_01
import BHHShard.K5R2.G252_02

namespace BHH.Shards

theorem k5r2_l252 : (7718575375728518113567641617855306759133760584445929967853087824654298933 : Int) ≤ BHH.Cert.shardN5r2 4128768 4145152 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) BHH.Shards.k5r2_g252_00 BHH.Shards.k5r2_g252_01) BHH.Shards.k5r2_g252_02)

end BHH.Shards
