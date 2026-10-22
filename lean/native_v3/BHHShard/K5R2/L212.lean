import BHH.ShardChainR2
import BHHShard.K5R2.G212_00
import BHHShard.K5R2.G212_01

namespace BHH.Shards

theorem k5r2_l212 : (4167788832459187053059620602686526083534436006267404909720055642441873602 : Int) ≤ BHH.Cert.shardN5r2 3473408 3489792 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) BHH.Shards.k5r2_g212_00 BHH.Shards.k5r2_g212_01)

end BHH.Shards
