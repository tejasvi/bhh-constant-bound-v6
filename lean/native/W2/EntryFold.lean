/-
The remainder fold of `entryF` (`pairStep` over the pairs `0, 1, 2`), the segment distance bounds of the three
pairs, and the comparison of the real remainder of T6 with the code's remainder.
-/
import W2.EntryArith
import W2.EntryBase

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W2

open W2C BHH.Cert BHH

/-! ## The fold -/

/-- The term of pair `p` (when `0 < d⁻ < 2`). -/
def pairTerm (prune : Bool) (C : ECore) (p : ℕ) : ℤ :=
  let dn := C.dmn.getD p 0
  let dx := C.dmx.getD p 0
  let S1 := C.S1s.getD p 0
  let S2 := C.S2s.getD p 0
  (nuOf prune C.pts (if prune then C.epsR else [0, 0, 0]) (lamOf dx) (muOf dn dx) dn p : ℤ) *
    ((if useFirstOf dx then shrU (lamOf dx * S2) PR + 1 else shrU (muOf dn dx * S1) PR + 1) +
      Min.min ((Iv.div ⟨S2, S2⟩ ⟨dn, dn⟩).hi) (shrU (piHi * S1) PR + 1))

lemma pairStep_none (prune : Bool) (C : ECore) (p : ℕ) : pairStep prune C none p = none := rfl

lemma pairStep_some (prune : Bool) (C : ECore) (er : ℤ) (p : ℕ) :
    pairStep prune C (some er) p =
      if 2 * ONE ≤ C.dmn.getD p 0 then some er
      else if C.dmn.getD p 0 ≤ 0 then none else some (er + pairTerm prune C p) := rfl

/-- What a successful fold tells: every pair has `d⁻ ≥ 2` or `d⁻ > 0`, and `er` is the sum of the terms of the
pairs with `d⁻ < 2`. -/
theorem fold_spec (prune : Bool) (C : ECore) {er : ℤ}
    (h : [0, 1, 2].foldl (pairStep prune C) (some 0) = some er) :
    (∀ p, p < 3 → 2 * ONE ≤ C.dmn.getD p 0 ∨ 0 < C.dmn.getD p 0) ∧
    er = ∑ p ∈ Finset.range 3, (if 2 * ONE ≤ C.dmn.getD p 0 then 0 else pairTerm prune C p) := by
  simp only [List.foldl_cons, List.foldl_nil] at h
  have step : ∀ (o : Option ℤ) (p : ℕ) (er' : ℤ), pairStep prune C o p = some er' →
      ∃ e, o = some e ∧ (2 * ONE ≤ C.dmn.getD p 0 ∨ 0 < C.dmn.getD p 0) ∧
        er' = e + (if 2 * ONE ≤ C.dmn.getD p 0 then 0 else pairTerm prune C p) := by
    intro o p er' hs
    cases o with
    | none => rw [pairStep_none] at hs; exact absurd hs (by simp)
    | some e =>
      refine ⟨e, rfl, ?_⟩
      rw [pairStep_some] at hs
      by_cases h1 : 2 * ONE ≤ C.dmn.getD p 0
      · rw [if_pos h1] at hs
        exact ⟨Or.inl h1, by rw [if_pos h1]; simp at hs; omega⟩
      · rw [if_neg h1] at hs
        by_cases h2 : C.dmn.getD p 0 ≤ 0
        · rw [if_pos h2] at hs; exact absurd hs (by simp)
        · rw [if_neg h2] at hs
          refine ⟨Or.inr (by omega), ?_⟩
          rw [if_neg h1]; simp at hs; omega
  obtain ⟨e2, he2, hp2, h2⟩ := step _ 2 er h
  obtain ⟨e1, he1, hp1, h1⟩ := step _ 1 e2 he2
  obtain ⟨e0, he0, hp0, h0⟩ := step _ 0 e1 he1
  have : e0 = 0 := Option.some.inj he0.symm
  refine ⟨fun p hp => ?_, ?_⟩
  · interval_cases p
    · exact hp0
    · exact hp1
    · exact hp2
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    omega

/-! ## `pairRem ≥ 0` -/

lemma pairRem_nonneg {dlo dhi S1 S2 : ℝ} {first : Bool} (hdlo : 0 < dlo) (hle : dlo ≤ dhi) (h2 : dlo < 2)
    (hf : first = true → dhi < 2) (hS1 : 0 ≤ S1) (hS2 : 0 ≤ S2) : 0 ≤ pairRem dlo dhi first S1 S2 := by
  unfold pairRem
  apply add_nonneg
  · split_ifs with h
    · exact div_nonneg hS2 (Real.sqrt_nonneg _)
    · apply mul_nonneg _ hS1
      have : dlo / 2 ≤ min dhi 2 / 2 := by
        apply div_le_div_of_nonneg_right (le_min hle h2.le) (by norm_num)
      have := Real.arcsin_le_arcsin this
      linarith
  · exact le_min (div_nonneg hS2 hdlo.le) (mul_nonneg Real.pi_pos.le hS1)

end BHH.W2
