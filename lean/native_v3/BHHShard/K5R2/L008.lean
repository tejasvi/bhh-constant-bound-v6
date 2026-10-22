import BHH.ShardChainR2
import BHHShard.K5R2.S008001
import BHHShard.K5R2.S008002
import BHHShard.K5R2.S008003
import BHHShard.K5R2.S008004
import BHHShard.K5R2.S008005
import BHHShard.K5R2.S008006

namespace BHH.Shards

theorem k5r2_l008 : (93809060083927182391155941226487685258485162811080903538665718282029553 : Int) ≤ BHH.Cert.shardN5r2 131072 147456 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 131072 137312) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s008001)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s008002)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s008003)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s008004)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s008005)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s008006))

end BHH.Shards
