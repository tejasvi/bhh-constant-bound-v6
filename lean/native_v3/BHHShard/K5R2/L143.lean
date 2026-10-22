import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l143 : (0 : Int) ≤ BHH.Cert.shardN5r2 2342912 2359296 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2342912 2359296)

end BHH.Shards
