import BHH.ShardChainR2
import BHHShard.K5R2.G026_00
import BHHShard.K5R2.G026_01

namespace BHH.Shards

theorem k5r2_l026 : (5839015735192832735946975134861123358238965723188614853016751841105672431 : Int) ≤ BHH.Cert.shardN5r2 425984 442368 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) BHH.Shards.k5r2_g026_00 BHH.Shards.k5r2_g026_01)

end BHH.Shards
