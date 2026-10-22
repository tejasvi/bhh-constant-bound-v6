/-
Module D: on a product cell, the pass value of the sure edges bounds `ĝ` from below.
-/
import W2.DiscCells
import W2.Interfaces

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W2

/-! ## Differences of partial sums -/

lemma psum_succ_sub {m : ℕ} (z : Fin m → Pt) {b : ℕ} (hb : b < m) :
    psum z ⟨b + 1, by omega⟩ - psum z ⟨b, by omega⟩ = z ⟨b, hb⟩ := by
  unfold psum
  rw [← Finset.sum_sub_distrib]
  have e : ∀ j : Fin m, ((if j.val < b + 1 then z j else 0) - (if j.val < b then z j else 0)) =
      if j = ⟨b, hb⟩ then z j else 0 := by
    intro j
    have : j = ⟨b, hb⟩ ↔ j.val = b := Fin.ext_iff
    by_cases h1 : j.val = b
    · simp [this.2 h1]
    · have h2 : j ≠ ⟨b, hb⟩ := fun h => h1 (this.1 h)
      by_cases h3 : j.val < b
      · simp [h3, show j.val < b + 1 by omega, h2]
      · simp [h3, show ¬ j.val < b + 1 by omega, h2]
  simp only [e]
  rw [Finset.sum_ite_eq' Finset.univ]
  simp

lemma psum_two_sub {m : ℕ} (z : Fin m → Pt) {b : ℕ} (hb : b + 1 < m) :
    psum z ⟨b + 2, by omega⟩ - psum z ⟨b, by omega⟩ = z ⟨b, by omega⟩ + z ⟨b + 1, hb⟩ := by
  have h1 := psum_succ_sub z hb
  have h2 := psum_succ_sub z (show b < m by omega)
  have e : psum z ⟨b + 2, by omega⟩ - psum z ⟨b, by omega⟩ =
      (psum z ⟨b + 1 + 1, by omega⟩ - psum z ⟨b + 1, by omega⟩) + (psum z ⟨b + 1, by omega⟩ - psum z ⟨b, by omega⟩) := by
    abel
  rw [e, h1, h2, add_comm]

lemma sqDist_eq_sub (p q : Pt) : sqDist p q = sqDist (p - q) 0 := by
  simp [sqDist]

lemma sqDist_comm' (p q : Pt) : sqDist p q = sqDist q p := by
  unfold sqDist; ring

/-! ## The sure edges are edges of the window graph -/

section Sure

variable {g : GridR} (hNR : 0 < g.NR) (hNT : 0 < g.NT) {D : DiscData} {m : ℕ}

lemma cget_of_lt (c : CellSeq g m) {j : ℕ} (hj : j < m) : cget hNR hNT c j = c ⟨j, hj⟩ := by
  simp [cget, hj]

/-- the edge `{b+1, b}` -/
lemma unit_adj_one (hD : TableSound g D) (c : CellSeq g m) {z : Fin m → Pt}
    (hz : ∀ j, z j ∈ g.cell (c j).1.val (c j).2.val) {b : ℕ} (hb : b < m)
    (ha : edgeA1 hNR hNT D c (b + 1) = true) :
    sqDist (psum z ⟨b + 1, by omega⟩) (psum z ⟨b, by omega⟩) ≤ 1 := by
  simp only [edgeA1, show 1 ≤ b + 1 by omega, ↓reduceIte, Nat.add_sub_cancel, cget_of_lt hNR hNT c hb] at ha
  rw [sqDist_eq_sub, psum_succ_sub z hb]
  exact hD.nf _ _ (c ⟨b, hb⟩).1.isLt (c ⟨b, hb⟩).2.isLt ha _ (hz ⟨b, hb⟩)

/-- the edge `{b+2, b}` -/
lemma unit_adj_two (hD : TableSound g D) (c : CellSeq g m) {z : Fin m → Pt}
    (hz : ∀ j, z j ∈ g.cell (c j).1.val (c j).2.val) {b : ℕ} (hb : b + 1 < m)
    (ha : edgeA2 hNR hNT D c (b + 2) = true) :
    sqDist (psum z ⟨b + 2, by omega⟩) (psum z ⟨b, by omega⟩) ≤ 1 := by
  simp only [edgeA2, show 2 ≤ b + 2 by omega, ↓reduceIte, Nat.add_sub_cancel,
    show b + 2 - 1 = b + 1 by omega, cget_of_lt hNR hNT c hb, cget_of_lt hNR hNT c (show b < m by omega)] at ha
  rw [sqDist_eq_sub, psum_two_sub z hb]
  exact hD.sc _ _ _ _ (c ⟨b, by omega⟩).1.isLt (c ⟨b + 1, hb⟩).1.isLt (c ⟨b, by omega⟩).2.isLt
    (c ⟨b + 1, hb⟩).2.isLt ha _ (hz _) _ (hz _)

lemma seqGraph_le_window (hD : TableSound g D) (c : CellSeq g m) {z : Fin m → Pt}
    (hz : ∀ j, z j ∈ g.cell (c j).1.val (c j).2.val) :
    seqGraph (edgeA1 hNR hNT D c) (edgeA2 hNR hNT D c) (m + 1) ≤ windowGraph (unitGraph (psum z)) := by
  intro a b hab
  have hnear := seqAdj_near hab
  have hne : a ≠ b := fun h => by subst h; exact SimpleGraph.irrefl _ hab
  refine ⟨⟨hne, ?_⟩, hnear⟩
  have ha := a.isLt
  have hb := b.isLt
  rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `a = b + 1`
    have e1 : a = ⟨b.val + 1, by omega⟩ := Fin.ext h1.symm
    have e2 : b = ⟨b.val, by omega⟩ := rfl
    rw [e1] at h2 ⊢
    exact unit_adj_one hNR hNT hD c hz (by omega) h2
  · -- `a = b + 2`
    have e1 : a = ⟨b.val + 2, by omega⟩ := Fin.ext h1.symm
    rw [e1] at h2 ⊢
    exact unit_adj_two hNR hNT hD c hz (by omega) h2
  · -- `b = a + 1`
    have e1 : b = ⟨a.val + 1, by omega⟩ := Fin.ext h1.symm
    rw [e1] at h2 ⊢
    rw [sqDist_comm']
    exact unit_adj_one hNR hNT hD c hz (by omega) h2
  · -- `b = a + 2`
    have e1 : b = ⟨a.val + 2, by omega⟩ := Fin.ext h1.symm
    rw [e1] at h2 ⊢
    rw [sqDist_comm']
    exact unit_adj_two hNR hNT hD c hz (by omega) h2

/-- on a product cell, half the pass value of the sure edges is at most `ĝ` -/
theorem pass_le_ghat (hD : TableSound g D) (c : CellSeq g m) {z : Fin m → Pt}
    (hz : ∀ j, z j ∈ g.cell (c j).1.val (c j).2.val) (hm : 1 ≤ m) :
    (passVal2 (edgeA1 hNR hNT D c) (edgeA2 hNR hNT D c) (m + 1) : ℝ) / 2 ≤ ghat z := by
  have h1 := passVal2_le_Lam (a1 := edgeA1 hNR hNT D c) (a2 := edgeA2 hNR hNT D c) (show 2 ≤ m + 1 by omega)
  have h2 := Lam_mono (seqGraph_le_window hNR hNT hD c hz)
  unfold ghat
  linarith

end Sure

end BHH.W2
