import BHH.ShardChainR2
import BHHShard.K5R2.G220_00
import BHHShard.K5R2.G220_01

namespace BHH.Shards

theorem k5r2_l220 : (3335392438721973409400311194182955584194917015592164026725931216116137991 : Int) ≤ BHH.Cert.shardN5r2 3604480 3620864 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) BHH.Shards.k5r2_g220_00 BHH.Shards.k5r2_g220_01)

end BHH.Shards
