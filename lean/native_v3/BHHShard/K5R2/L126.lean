import BHH.ShardChainR2
import BHHShard.K5R2.G126_00
import BHHShard.K5R2.G126_01

namespace BHH.Shards

theorem k5r2_l126 : (1755845235888877864007010279197860769589119493318052141285529330711422571 : Int) ≤ BHH.Cert.shardN5r2 2064384 2080768 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) BHH.Shards.k5r2_g126_00 BHH.Shards.k5r2_g126_01)

end BHH.Shards
