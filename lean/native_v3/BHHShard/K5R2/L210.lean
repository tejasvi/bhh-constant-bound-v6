import BHH.ShardChainR2
import BHHShard.K5R2.S210001
import BHHShard.K5R2.S210002

namespace BHH.Shards

theorem k5r2_l210 : (66749776274580759785949003932615117609588984496585974546323084901048320 : Int) ≤ BHH.Cert.shardN5r2 3440640 3457024 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 3440640 3452448) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s210001)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s210002))

end BHH.Shards
