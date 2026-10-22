import BHH.ShardChainR2
import BHHShard.K5R2.G058_00
import BHHShard.K5R2.G058_01
import BHHShard.K5R2.G058_02

namespace BHH.Shards

theorem k5r2_l058 : (13236540997098364243388804968592180806984983521596006130842711956503681762 : Int) ≤ BHH.Cert.shardN5r2 950272 966656 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) BHH.Shards.k5r2_g058_00 BHH.Shards.k5r2_g058_01) BHH.Shards.k5r2_g058_02)

end BHH.Shards
