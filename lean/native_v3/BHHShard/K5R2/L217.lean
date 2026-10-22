import BHH.ShardChainR2
import BHHShard.K5R2.S217001
import BHHShard.K5R2.S217002

namespace BHH.Shards

theorem k5r2_l217 : (36849052358524046408343903960216341245630104666622204702009136058819223 : Int) ≤ BHH.Cert.shardN5r2 3555328 3571712 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 3555328 3559424) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s217001)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s217002))

end BHH.Shards
