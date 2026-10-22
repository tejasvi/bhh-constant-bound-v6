import BHH.ShardChainR2
import BHHShard.K5R2.S04002001
import BHHShard.K5R2.S04006001
import BHHShard.K5R2.S04010001
import BHHShard.K5R2.S04010002
import BHHShard.K5R2.S04010003
import BHHShard.K5R2.S04010004
import BHHShard.K5R2.S04010005
import BHHShard.K5R2.S04010006
import BHHShard.K5R2.S04010007
import BHHShard.K5R2.S04010008
import BHHShard.K5R2.S04010009
import BHHShard.K5R2.S04010010
import BHHShard.K5R2.S04010011
import BHHShard.K5R2.S04010012
import BHHShard.K5R2.S04010013
import BHHShard.K5R2.S04010014
import BHHShard.K5R2.S04010015
import BHHShard.K5R2.S04010016
import BHHShard.K5R2.S04010017
import BHHShard.K5R2.S04011001
import BHHShard.K5R2.S04014001

namespace BHH.Shards

theorem k5r2_l040 : (384629454179181465092104284477817186099046027129007612507618138290614230 : Int) ≤ BHH.Cert.shardN5r2 655360 671744 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 655360 656384) (BHH.shardN5r2_nonneg 656384 657408)) (BHH.shardN5r2_nonneg 657408 657472)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s04002001)) (BHH.shardN5r2_nonneg 658432 659456)) (BHH.shardN5r2_nonneg 659456 660480)) (BHH.shardN5r2_nonneg 660480 661504)) (BHH.shardN5r2_nonneg 661504 661827)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s04006001)) (BHH.shardN5r2_nonneg 662528 663552)) (BHH.shardN5r2_nonneg 663552 664576)) (BHH.shardN5r2_nonneg 664576 665600)) (BHH.shardN5r2_nonneg 665600 665602)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s04010001)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s04010002)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s04010003)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s04010004)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s04010005)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s04010006)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s04010007)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s04010008)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s04010009)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s04010010)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s04010011)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s04010012)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s04010013)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s04010014)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s04010015)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s04010016)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s04010017)) (BHH.shardN5r2_nonneg 666624 666882)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s04011001)) (BHH.shardN5r2_nonneg 667648 668672)) (BHH.shardN5r2_nonneg 668672 669696)) (BHH.shardN5r2_nonneg 669696 669954)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s04014001)) (BHH.shardN5r2_nonneg 670720 671744))

end BHH.Shards
