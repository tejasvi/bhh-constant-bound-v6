import BHH.ShardChainR2
import BHHShard.K5R2.S115001
import BHHShard.K5R2.S115002

namespace BHH.Shards

theorem k5r2_l115 : (38623852199863335581606713689573630894353577982407998790152131663938436 : Int) ≤ BHH.Cert.shardN5r2 1884160 1900544 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 1884160 1885218) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s115001)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s115002))

end BHH.Shards
