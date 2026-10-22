import BHH.ShardChainR2
import BHHShard.K5R2.S253000
import BHHShard.K5R2.S253001

namespace BHH.Shards

theorem k5r2_l253 : (42160162755255850570726823075120191446389208860185344903642213397720714 : Int) ≤ BHH.Cert.shardN5r2 4145152 4161536 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s253000) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s253001))

end BHH.Shards
