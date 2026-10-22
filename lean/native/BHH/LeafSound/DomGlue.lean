/-
Module D, part 14: the domain tests of the leaf (`outside`, the straddling pairs) against `D_k`.
-/
import BHH.LeafSound.Specs

open BHH.Cert Real MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BHH

lemma ptBoxes_xl_xh {k : ℕ} (lo hi : List ℤ) {j : ℕ} (hj2 : 2 ≤ j) (hjk : j < k) :
    ((ptBoxes k lo hi).getD j default).xl = listGet lo (2 * j - 3) ∧
    ((ptBoxes k lo hi).getD j default).xh = listGet hi (2 * j - 3) ∧
    ((ptBoxes k lo hi).getD j default).yl = listGet lo (2 * j - 2) := by
  have h := ptBoxes_getD k lo hi ⟨j, hjk⟩
  simp only at h
  rw [h]
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  simp [h0, h1]

/-- no point outside the box's `D_k` tests and no straddling pair: the box lies in `D_k` -/
lemma boxOf_subset_Dk {k : ℕ} (hk : 3 ≤ k) {lo hi : List ℤ} (hv : ValidBox k lo hi)
    (hlo0 : 0 ≤ listGet lo 0) (hlo2 : 0 ≤ listGet lo 2)
    (hord : ∀ j, 2 ≤ j → j + 1 < k → listGet hi (2 * j - 3) ≤ listGet lo (2 * (j + 1) - 3)) :
    (boxOf lo hi : Set (Fin (mDim k) → ℝ)) ⊆ Dk k := by
  intro x hx
  rw [mem_boxOf_iff] at hx
  have hm : mDim k = 2 * k - 3 := rfl
  refine ⟨?_, ?_, ?_⟩
  · have h0 : 0 < mDim k := by rw [hm]; omega
    rw [xget_of_lt x h0]
    have := (hx ⟨0, h0⟩).1
    exact le_trans (fx_nonneg_iff.mpr hlo0) this
  · have h2 : 2 < mDim k := by rw [hm]; omega
    rw [xget_of_lt x h2]
    have := (hx ⟨2, h2⟩).1
    exact le_trans (fx_nonneg_iff.mpr hlo2) this
  · intro j hj2 hjk
    have ha : 2 * j - 3 < mDim k := by rw [hm]; omega
    have hb : 2 * (j + 1) - 3 < mDim k := by rw [hm]; omega
    rw [xget_of_lt x ha, xget_of_lt x hb]
    have h1 := (hx ⟨2 * j - 3, ha⟩).2
    have h2 := (hx ⟨2 * (j + 1) - 3, hb⟩).1
    have h3 : fx (hi.getD (2 * j - 3) 0) ≤ fx (lo.getD (2 * (j + 1) - 3) 0) := fx_le_iff.mpr (hord j hj2 hjk)
    simp only at h1 h2
    linarith

/-- the code's ordered pairs `2 ≤ j`, `j + 1 < k` -/
abbrev ordPairsC (k : ℕ) : List ℕ := List.filter (fun j => decide (2 ≤ j ∧ j + 1 < k)) (List.range k)

/-- the code's straddling pairs -/
abbrev stradC (k : ℕ) (lo hi : List ℤ) : List ℕ :=
  List.filter (fun j => decide (((ptBoxes k lo hi).getD j default).xh > ((ptBoxes k lo hi).getD (j + 1) default).xl))
    (ordPairsC k)

lemma mem_ordPairsC {k j : ℕ} : j ∈ ordPairsC k ↔ 2 ≤ j ∧ j + 1 < k := by
  simp only [ordPairsC, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨by omega, h⟩

lemma ord_of_not_strad {k : ℕ} {lo hi : List ℤ} {j : ℕ} (hj : j ∈ ordPairsC k) (hn : j ∉ stradC k lo hi) :
    listGet hi (2 * j - 3) ≤ listGet lo (2 * (j + 1) - 3) := by
  obtain ⟨hj2, hjk⟩ := mem_ordPairsC.mp hj
  have h : ¬ (((ptBoxes k lo hi).getD j default).xh > ((ptBoxes k lo hi).getD (j + 1) default).xl) := by
    intro hc; apply hn
    exact List.mem_filter.mpr ⟨hj, by simpa using hc⟩
  obtain ⟨_, hxh, _⟩ := ptBoxes_xl_xh lo hi hj2 (by omega : j < k)
  obtain ⟨hxl, _, _⟩ := ptBoxes_xl_xh lo hi (by omega : 2 ≤ j + 1) hjk
  rw [hxh, hxl] at h
  exact not_lt.mp h

/-- no straddling pair: all ordered pairs are in order on the box -/
lemma ord_of_strad_nil {k : ℕ} {lo hi : List ℤ} (h : (stradC k lo hi).length = 0) :
    ∀ j, 2 ≤ j → j + 1 < k → listGet hi (2 * j - 3) ≤ listGet lo (2 * (j + 1) - 3) := by
  intro j hj2 hjk
  have hnil : stradC k lo hi = [] := List.eq_nil_of_length_eq_zero h
  exact ord_of_not_strad (mem_ordPairsC.mpr ⟨hj2, hjk⟩) (by rw [hnil]; simp)

/-- one straddling pair `j0`: it is an ordered pair and all others are in order -/
lemma ord_of_strad_single {k : ℕ} {lo hi : List ℤ} {j0 : ℕ} (h : stradC k lo hi = [j0]) :
    (2 ≤ j0 ∧ j0 + 1 < k) ∧
    ∀ j, 2 ≤ j → j + 1 < k → j ≠ j0 → listGet hi (2 * j - 3) ≤ listGet lo (2 * (j + 1) - 3) := by
  have hmem : j0 ∈ stradC k lo hi := by rw [h]; simp
  have hj0 : j0 ∈ ordPairsC k := (List.mem_filter.mp hmem).1
  refine ⟨mem_ordPairsC.mp hj0, ?_⟩
  intro j hj2 hjk hne
  exact ord_of_not_strad (mem_ordPairsC.mpr ⟨hj2, hjk⟩) (by rw [h]; simp [hne])

/-- the code's `outside` test fails: `r_2 ≥ 0` and `η_2 ≥ 0` at the lower corner -/
lemma lo_nonneg_of_not_outside {k : ℕ} (hk : 3 ≤ k) {lo hi : List ℤ}
    (h : ¬((listGet lo 0 < 0 ∨ 2 < k ∧ ((ptBoxes k lo hi).getD 2 default).yl < 0) ∨
      ((ordPairsC k).any fun j =>
          decide (((ptBoxes k lo hi).getD j default).xl > ((ptBoxes k lo hi).getD (j + 1) default).xh)) = true)) :
    0 ≤ listGet lo 0 ∧ 0 ≤ listGet lo 2 := by
  push_neg at h
  obtain ⟨⟨h0, h2⟩, _⟩ := h
  refine ⟨h0, ?_⟩
  have := h2 (by omega)
  obtain ⟨_, _, hyl⟩ := ptBoxes_xl_xh (k := k) lo hi (le_refl 2) (by omega)
  rw [hyl] at this
  simpa using this

lemma measurable_xget' {m : ℕ} (d : ℕ) : Measurable fun x : Fin m → ℝ => xget x d := by
  unfold xget
  by_cases h : d < m
  · simp only [h, dite_true]; exact measurable_pi_apply _
  · simp only [h, dite_false]; exact measurable_const

lemma measurableSet_Dk_leaf (k : ℕ) : MeasurableSet (Dk k) := by
  have e : Dk k = ({x | 0 ≤ xget x 0} ∩ {x | 0 ≤ xget x 2}) ∩
      ⋂ j : ℕ, {x | 2 ≤ j → j + 1 < k → xget x (2 * j - 3) ≤ xget x (2 * (j + 1) - 3)} := by
    ext x
    simp only [Dk, mem_setOf_eq, mem_inter_iff, mem_iInter, and_assoc]
  rw [e]
  refine ((measurableSet_le measurable_const (measurable_xget' 0)).inter
    (measurableSet_le measurable_const (measurable_xget' 2))).inter (MeasurableSet.iInter fun j => ?_)
  by_cases h : 2 ≤ j ∧ j + 1 < k
  · have e2 : {x : Fin (mDim k) → ℝ | 2 ≤ j → j + 1 < k → xget x (2 * j - 3) ≤ xget x (2 * (j + 1) - 3)} =
        {x | xget x (2 * j - 3) ≤ xget x (2 * (j + 1) - 3)} := by
      ext x; simp only [mem_setOf_eq, h.1, h.2, true_implies]
    rw [e2]
    exact measurableSet_le (measurable_xget' _) (measurable_xget' _)
  · have e2 : {x : Fin (mDim k) → ℝ | 2 ≤ j → j + 1 < k → xget x (2 * j - 3) ≤ xget x (2 * (j + 1) - 3)} =
        univ := by
      ext x; simp only [mem_setOf_eq, mem_univ, iff_true]
      intro h1 h2; exact absurd ⟨h1, h2⟩ h
    rw [e2]
    exact MeasurableSet.univ

end BHH
