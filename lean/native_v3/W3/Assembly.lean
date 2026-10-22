/-
Assembly of Theorem 1.1 of the paper from the box part and the window-3 part, for any window-3 constant `w ≥ 0`:
`betaBoundV3At_of : MainBoundsV3 → W3BoundAt w → BetaBoundV3At b` for every `b ≤ 5/8 + C3 + C4 + C5 + w` (the pattern of
`betaBoundV2_of` in BHH/MainV2.lean; the terms `23 ≤ k ≤ 30` of `DongCaoK30` are dropped, `C_k ≥ 0`), and
`bhhBetaBoundV3At_of : BetaBoundV3At b → BHHBetaBoundV3At b`.  The paper's constants: `betaBoundV3_of`.
-/
import BHH.StatementW3

open scoped ENNReal

namespace BHH.W3

/-- `BetaBoundV3At b` from the box part and the window-3 part with constant `w`, for `b ≤ 5/8 + C3 + C4 + C5 + w`. -/
theorem betaBoundV3At_of {w b : ℝ} (hw : 0 ≤ w)
    (hb : b ≤ 5 / 8 + 117130195 / 10 ^ 10 + 63707166 / 10 ^ 10 + 35280362 / 10 ^ 10 + w)
    (hM : MainBoundsV3) (hW : W3BoundAt w) : BetaBoundV3At b := by
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
  have hsub : ∑ k ∈ Finset.Icc 6 22, C k ≤ ∑ k ∈ Finset.Icc 6 30, C k :=
    Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc le_rfl (by norm_num))
  have hsum : ENNReal.ofReal (5 / 8 + 117130195 / 10 ^ 10 + 63707166 / 10 ^ 10 + 35280362 / 10 ^ 10 + w) =
      (5 / 8 : ℝ≥0∞) + (ENNReal.ofReal (117130195 / 10 ^ 10) + (ENNReal.ofReal (63707166 / 10 ^ 10) +
        (ENNReal.ofReal (35280362 / 10 ^ 10) + ENNReal.ofReal w))) := by
    have e58 : (5 / 8 : ℝ≥0∞) = ENNReal.ofReal (5 / 8) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
    rw [e58, ← ENNReal.ofReal_add (by norm_num) hw, ← ENNReal.ofReal_add (by norm_num) (by positivity),
      ← ENNReal.ofReal_add (by norm_num) (by positivity), ← ENNReal.ofReal_add (by norm_num) (by positivity)]
    congr 1
    ring
  have hle : ENNReal.ofReal (5 / 8 + 117130195 / 10 ^ 10 + 63707166 / 10 ^ 10 + 35280362 / 10 ^ 10 + w) ≤
      ENNReal.ofReal β := by
    rw [hsum]
    refine le_trans ?_ hβ
    gcongr
    exact h6.trans hsub
  have hβpos : 0 < β :=
    ENNReal.ofReal_pos.mp (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) hle)
  exact hb.trans ((ENNReal.ofReal_le_ofReal_iff hβpos.le).mp hle)

/-- `BHHBetaBoundV3At b` from `BetaBoundV3At b`. -/
theorem bhhBetaBoundV3At_of {b : ℝ} (hB : BetaBoundV3At b) : BHHBetaBoundV3At b :=
  fun hG hV hDC β hβ => hB hG hV β (hDC β hβ)

/-- The paper's constants: `BetaBoundV3` from the box part and `W3Bound`. -/
theorem betaBoundV3_of (hM : MainBoundsV3) (hW : W3Bound) : BetaBoundV3 :=
  betaBoundV3At_of (by norm_num) (by norm_num) hM hW

/-- `BHHBetaBoundV3` from `BetaBoundV3`. -/
theorem bhhBetaBoundV3_of (hB : BetaBoundV3) : BHHBetaBoundV3 := bhhBetaBoundV3At_of hB

end BHH.W3
