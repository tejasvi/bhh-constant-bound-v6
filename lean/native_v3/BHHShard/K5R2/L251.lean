import BHH.ShardChainR2
import BHHShard.K5R2.S251001

namespace BHH.Shards

theorem k5r2_l251 : (331534949206071740676286624074357857053308396642114623150496615088676 : Int) ≤ BHH.Cert.shardN5r2 4112384 4128768 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 4112384 4122628) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s251001))

end BHH.Shards
