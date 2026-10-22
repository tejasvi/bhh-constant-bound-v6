import BHH.ShardChainR2
import BHHShard.K5R2.S00003001
import BHHShard.K5R2.S00005001
import BHHShard.K5R2.S00007001
import BHHShard.K5R2.S00007002
import BHHShard.K5R2.S00007003
import BHHShard.K5R2.S00007004
import BHHShard.K5R2.S00007005
import BHHShard.K5R2.S00007006
import BHHShard.K5R2.S00007007
import BHHShard.K5R2.S00007008
import BHHShard.K5R2.S00007009
import BHHShard.K5R2.S00007010
import BHHShard.K5R2.S00007011

namespace BHH.Shards

theorem k5r2_l000 : (88453034879248617456547806087250189333552544734566214550019568499334037 : Int) ≤ BHH.Cert.shardN5r2 0 16384 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 0 2048) (BHH.shardN5r2_nonneg 2048 4096)) (BHH.shardN5r2_nonneg 4096 6144)) (BHH.shardN5r2_nonneg 6144 7272)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s00003001)) (BHH.shardN5r2_nonneg 8192 10240)) (BHH.shardN5r2_nonneg 10240 11562)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s00005001)) (BHH.shardN5r2_nonneg 12288 14336)) (BHH.shardN5r2_nonneg 14336 14634)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s00007001)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s00007002)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s00007003)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s00007004)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s00007005)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s00007006)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s00007007)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s00007008)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s00007009)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s00007010)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s00007011))

end BHH.Shards
