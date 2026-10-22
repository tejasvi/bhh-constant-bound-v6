/-
Module D, part 8: the volume factor of the leaf (`finish`): `finish lb / 2^OS ≤ vol(box) · fx lb`.
-/
import BHH.LeafSound.RemSum

open BHH.Cert Real MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BHH

/-- the exact volume numerator of the code: `∏_{d < n} (hi_d - lo_d)` -/
lemma foldl_vnum (lo hi : List ℤ) (n : ℕ) (a : ℤ) :
    (List.range n).foldl (fun acc d => acc * (listGet hi d - listGet lo d)) a =
      a * ∏ d ∈ Finset.range n, (listGet hi d - listGet lo d) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, Finset.prod_range_succ]
    simp [mul_assoc]

/-- the volume of a valid box -/
lemma volume_boxOf_toReal {k : ℕ} {lo hi : List ℤ} (hv : ValidBox k lo hi) :
    (volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal =
      (((List.range (mDim k)).foldl (fun acc d => acc * (listGet hi d - listGet lo d)) 1 : ℤ) : ℝ) /
        (2 : ℝ) ^ (mDim k * PR) := by
  unfold boxOf
  rw [Real.volume_pi_Ico, ENNReal.toReal_prod, foldl_vnum, one_mul]
  have hpos : ∀ d : Fin (mDim k), 0 ≤ fx (hi.getD d.val 0) - fx (lo.getD d.val 0) := by
    intro d
    have := (hv.2.2.1 d.val d.isLt).1
    have : fx (lo.getD d.val 0) ≤ fx (hi.getD d.val 0) := fx_le_iff.mpr this.le
    linarith
  simp only [ENNReal.toReal_ofReal (hpos _)]
  rw [Fin.prod_univ_eq_prod_range (fun d => fx (hi.getD d 0) - fx (lo.getD d 0)) (mDim k)]
  push_cast
  have e : ∀ i, fx (hi.getD i 0) - fx (lo.getD i 0) = ((listGet hi i : ℝ) - (listGet lo i : ℝ)) / 2 ^ PR := by
    intro i; unfold fx listGet; ring
  simp only [e]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range, ← pow_mul, mul_comm PR (mDim k)]

/-- the volume factor: `finish lb / 2^OS ≤ vol · fx lb` -/
lemma finish_le {k : ℕ} (hk3 : 3 ≤ k) {lo hi : List ℤ} (hv : ValidBox k lo hi) (lb : ℤ) :
    ((shrD ((List.range (mDim k)).foldl (fun acc d => acc * (listGet hi d - listGet lo d)) 1 * lb)
      (mDim k * PR + PR - OS) : ℤ) : ℝ) / (2 : ℝ) ^ OS ≤
      (volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal * fx lb := by
  rw [volume_boxOf_toReal hv]
  have hk : OS ≤ mDim k * PR + PR := by
    have : 3 ≤ mDim k := by unfold mDim; omega
    simp only [OS, PR]; nlinarith
  have h := shrD_le ((List.range (mDim k)).foldl (fun acc d => acc * (listGet hi d - listGet lo d)) 1 * lb)
    (mDim k * PR + PR - OS)
  have h2 : (2 : ℝ) ^ (mDim k * PR + PR - OS) * 2 ^ OS = 2 ^ (mDim k * PR) * 2 ^ PR := by
    rw [← pow_add, ← pow_add, Nat.sub_add_cancel hk]
  calc _ ≤ (((List.range (mDim k)).foldl (fun acc d => acc * (listGet hi d - listGet lo d)) 1 * lb : ℤ) : ℝ) /
          2 ^ (mDim k * PR + PR - OS) / 2 ^ OS := by gcongr
    _ = _ := by
      unfold fx
      rw [div_div, h2]; push_cast; field_simp

end BHH
