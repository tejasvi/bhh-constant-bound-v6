import BHH.ShardChainR2
import BHHShard.K5R2.G018_00
import BHHShard.K5R2.G018_01

namespace BHH.Shards

theorem k5r2_l018 : (5943641216207877379010470940017904047922362827695338073060898019216258840 : Int) ≤ BHH.Cert.shardN5r2 294912 311296 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) BHH.Shards.k5r2_g018_00 BHH.Shards.k5r2_g018_01)

end BHH.Shards
