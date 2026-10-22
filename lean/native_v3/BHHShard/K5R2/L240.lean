import BHH.ShardChainR2
import BHHShard.K5R2.G240_00
import BHHShard.K5R2.G240_01
import BHHShard.K5R2.G240_02

namespace BHH.Shards

theorem k5r2_l240 : (16760965170991311482749746493695139963595710289069654758941747829719933304 : Int) ≤ BHH.Cert.shardN5r2 3932160 3948544 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) BHH.Shards.k5r2_g240_00 BHH.Shards.k5r2_g240_01) BHH.Shards.k5r2_g240_02)

end BHH.Shards
