import BHH.ShardChainR2
import BHHShard.K5R2.S127001

namespace BHH.Shards

theorem k5r2_l127 : (7753965992683351234346951579435600365117649465422398574251390097958163 : Int) ≤ BHH.Cert.shardN5r2 2080768 2097152 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 2080768 2080802) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s127001))

end BHH.Shards
