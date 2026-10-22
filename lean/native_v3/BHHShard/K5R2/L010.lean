import BHH.ShardChainR2
import BHHShard.K5R2.G010_00
import BHHShard.K5R2.G010_01

namespace BHH.Shards

theorem k5r2_l010 : (2056131154706941427635271632375788319467397298390212300490636410559807533 : Int) ≤ BHH.Cert.shardN5r2 163840 180224 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) BHH.Shards.k5r2_g010_00 BHH.Shards.k5r2_g010_01)

end BHH.Shards
