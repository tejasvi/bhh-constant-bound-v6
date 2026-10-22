import BHH.ShardChainR2
import BHHShard.K5R2.G122_00
import BHHShard.K5R2.G122_01
import BHHShard.K5R2.G122_02
import BHHShard.K5R2.G122_03
import BHHShard.K5R2.G122_04

namespace BHH.Shards

theorem k5r2_l122 : (22389138835662911508094065158820932402192660246894581310255021770539814507 : Int) ≤ BHH.Cert.shardN5r2 1998848 2015232 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) BHH.Shards.k5r2_g122_00 BHH.Shards.k5r2_g122_01) BHH.Shards.k5r2_g122_02) BHH.Shards.k5r2_g122_03) BHH.Shards.k5r2_g122_04)

end BHH.Shards
