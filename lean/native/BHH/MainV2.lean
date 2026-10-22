/-
Assembly of the native bound (module E).

* `C_ge_of_shardSum`: a shard sum `S ≤ shardSum k dec L R a b` (any decision function), leaf soundness, Lemma 2.2
  (`domainReductionProp_of_three_le`) and a lower bound `q ≤ κ_k` give `C_k ≥ (q/2) S / 2^OS`.
* `mainBoundsV2_of`: `MainBoundsV2` from leaf soundness of the N-track leaf functions `Lk k` (module D) and lower
  bounds `S_k ≤ shardN k 0 (2^RN k)` (the shard theorems), with the arithmetic checks `c3`, `c4`, `c5`.
* `betaBoundV2_of`: `BetaBoundV2` from `MainBoundsV2` and `W2Bound`; `bhhBetaBoundV2_of`: `BHHBetaBoundV2`.
-/
import BHH.Tree
import BHH.Kappa
import BHH.Domain
import BHH.StatementV2
import BHHCert.Shard

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.E

open BHH.Cert

/-- one term `C_k` from a shard sum, for every decision function -/
theorem C_ge_of_shardSum {k : ℕ} (hk : 3 ≤ k) {L : List ℤ → List ℤ → ℤ} (hL : LeafSoundProp k L)
    (dec : List ℤ → List ℤ → Dec) {R a b : ℕ} (hb : b ≤ 2 ^ R) {S : ℤ}
    (hS : S ≤ shardSum k dec L R a b) {q t : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ kappa k)
    (ht : t ≤ q / 2 * ((S : ℝ) / 2 ^ OS)) : ENNReal.ofReal t ≤ C k := by
  have hdom := domainReductionProp_of_three_le hk
  have hsh := shardSum_sound (by omega) hL dec (a := a) hb
  by_cases hS0 : S < 0
  · have h0 : q / 2 * ((S : ℝ) / 2 ^ OS) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity)
        (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hS0.le) (by positivity))
    rw [ENNReal.ofReal_of_nonpos (ht.trans h0)]
    exact zero_le
  push Not at hS0
  have hκ : 0 ≤ kappa k / 2 := by linarith
  have hSr : (0 : ℝ) ≤ (S : ℝ) / 2 ^ OS := div_nonneg (by exact_mod_cast hS0) (by positivity)
  calc ENNReal.ofReal t ≤ ENNReal.ofReal (kappa k / 2 * ((S : ℝ) / 2 ^ OS)) :=
        ENNReal.ofReal_le_ofReal (ht.trans (mul_le_mul_of_nonneg_right (by linarith) hSr))
    _ = ENNReal.ofReal (kappa k / 2) * ENNReal.ofReal ((S : ℝ) / 2 ^ OS) := ENNReal.ofReal_mul hκ
    _ ≤ ENNReal.ofReal (kappa k / 2) * ENNReal.ofReal ((shardSum k dec L R a b : ℝ) / 2 ^ OS) :=
        mul_le_mul_right (ENNReal.ofReal_le_ofReal
          (div_le_div_of_nonneg_right (by exact_mod_cast hS) (by positivity))) _
    _ ≤ ENNReal.ofReal (kappa k / 2) * ∫⁻ x in Dk k ∩ Xk k, F2 k x := mul_le_mul_right hsh _
    _ ≤ C k := hdom

/-- two adjacent shard ranges -/
theorem le_shardSum_add {k : ℕ} {dec : List ℤ → List ℤ → Dec} {L : List ℤ → List ℤ → ℤ} {R a b c : ℕ}
    {v v' : ℤ} (hab : a ≤ b) (hbc : b ≤ c) (h : v ≤ shardSum k dec L R a b)
    (h' : v' ≤ shardSum k dec L R b c) : v + v' ≤ shardSum k dec L R a c := by
  rw [← shardSum_add k dec L hab hbc]
  exact add_le_add h h'

/-- one term `C_k` from the N-track shard sum over all initial boxes -/
theorem C_ge_of_shardN {k : ℕ} (hk : 3 ≤ k) (hL : LeafSoundProp k (Lk k)) {S : ℤ}
    (hS : S ≤ shardN k 0 (2 ^ RN k)) {q t : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ kappa k)
    (ht : t ≤ q / 2 * ((S : ℝ) / 2 ^ OS)) : ENNReal.ofReal t ≤ C k :=
  C_ge_of_shardSum hk hL _ le_rfl hS hq0 hq ht

lemma piThreeHalvesLo_nonneg : 0 ≤ piThreeHalvesLo := by unfold piThreeHalvesLo; norm_num

/-- `MainBoundsV2` from leaf soundness (module D) and the shard bounds (track N) -/
theorem mainBoundsV2_of
    (hL : GreenFormula → VertexLemmaSeg → ∀ k : ℕ, 3 ≤ k → k ≤ 5 → LeafSoundProp k (Lk k))
    {S3 S4 S5 : ℤ} (h3 : S3 ≤ shardN 3 0 (2 ^ RN 3)) (h4 : S4 ≤ shardN 4 0 (2 ^ RN 4))
    (h5 : S5 ≤ shardN 5 0 (2 ^ RN 5))
    (c3 : (117130195 / 10 ^ 10 : ℝ) ≤ 1 / 4 * piThreeHalvesLo / 2 * ((S3 : ℝ) / 2 ^ OS))
    (c4 : (63707166 / 10 ^ 10 : ℝ) ≤ 5 / 16 * piThreeHalvesLo / 2 * ((S4 : ℝ) / 2 ^ OS))
    (c5 : (34034701 / 10 ^ 10 : ℝ) ≤ 21 / 32 * piThreeHalvesLo / 2 * ((S5 : ℝ) / 2 ^ OS)) :
    MainBoundsV2 := by
  intro hG hV
  have hp := piThreeHalvesLo_nonneg
  refine ⟨?_, ?_, ?_⟩
  · exact C_ge_of_shardN (by norm_num) (hL hG hV 3 le_rfl (by norm_num)) h3 (by positivity)
      kappa_three_gt.le c3
  · exact C_ge_of_shardN (by norm_num) (hL hG hV 4 (by norm_num) (by norm_num)) h4 (by positivity)
      kappa_four_gt.le c4
  · exact C_ge_of_shardN (by norm_num) (hL hG hV 5 (by norm_num) le_rfl) h5 (by positivity)
      kappa_five_gt.le c5

/-- `BetaBoundV2` from the box part and the window-2 part -/
theorem betaBoundV2_of (hM : MainBoundsV2) (hW : W2Bound) : BetaBoundV2 := by
  intro hG hV β hβ
  obtain ⟨h3, h4, h5⟩ := hM hG hV
  have h6 := hW hG hV
  unfold DongCaoK30 at hβ
  have e1 : Finset.Icc 3 30 = insert 3 (Finset.Icc 4 30) :=
    (Finset.insert_Icc_add_one_left_eq_Icc (by norm_num)).symm
  have e2 : Finset.Icc 4 30 = insert 4 (Finset.Icc 5 30) :=
    (Finset.insert_Icc_add_one_left_eq_Icc (by norm_num)).symm
  have e3 : Finset.Icc 5 30 = insert 5 (Finset.Icc 6 30) :=
    (Finset.insert_Icc_add_one_left_eq_Icc (by norm_num)).symm
  rw [e1, Finset.sum_insert (by simp), e2, Finset.sum_insert (by simp), e3,
    Finset.sum_insert (by simp)] at hβ
  have hsum : ENNReal.ofReal (6491725104 / 10 ^ 10) =
      (5 / 8 : ℝ≥0∞) + (ENNReal.ofReal (117130195 / 10 ^ 10) + (ENNReal.ofReal (63707166 / 10 ^ 10) +
        (ENNReal.ofReal (34034701 / 10 ^ 10) + ENNReal.ofReal (26853042 / 10 ^ 10)))) := by
    have e58 : (5 / 8 : ℝ≥0∞) = ENNReal.ofReal (5 / 8) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
    rw [e58, ← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ENNReal.ofReal_add (by norm_num) (by positivity)]
    norm_num
  have hle : ENNReal.ofReal (6491725104 / 10 ^ 10) ≤ ENNReal.ofReal β := by
    rw [hsum]
    refine le_trans ?_ hβ
    gcongr
  have hβpos : 0 < β := ENNReal.ofReal_pos.mp (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by norm_num)) hle)
  exact (ENNReal.ofReal_le_ofReal_iff hβpos.le).mp hle

/-- `BHHBetaBoundV2` from `BetaBoundV2` -/
theorem bhhBetaBoundV2_of (hB : BetaBoundV2) : BHHBetaBoundV2 :=
  fun hG hV hDC β hβ => hB hG hV β (hDC β hβ)

end BHH.E

namespace BHH

-- the deliverables of this file, also under `BHH` (helpers stay in `BHH.E`)
export E (C_ge_of_shardSum le_shardSum_add C_ge_of_shardN mainBoundsV2_of betaBoundV2_of bhhBetaBoundV2_of)

end BHH
