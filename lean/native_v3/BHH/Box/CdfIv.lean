/-
Module C: `cdfIv` encloses `cdfR` (`CdfIvProp`), from module A's interval lemmas.
-/
import BHH.Box.Cdf
import BHH.Ivl.Asin

open BHH.Cert

noncomputable section

namespace BHH

/-! ## fixed-point helpers -/

lemma fx_add (a b : ℤ) : fx (a + b) = fx a + fx b := by unfold fx; push_cast; ring

lemma fx_subC (a b : ℤ) : fx (a - b) = fx a - fx b := by unfold fx; push_cast; ring

lemma fx_zeroC : fx 0 = 0 := by simp [fx]

lemma fx_lt_iff {a b : ℤ} : fx a < fx b ↔ a < b := by
  rw [lt_iff_not_ge, lt_iff_not_ge, fx_le_iff]

lemma fx_min (a b : ℤ) : fx (min a b) = min (fx a) (fx b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (fx_le_iff.2 h)]
  · rw [min_eq_right h, min_eq_right (fx_le_iff.2 h)]

lemma fx_maxC (a b : ℤ) : fx (max a b) = max (fx a) (fx b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (fx_le_iff.2 h)]
  · rw [max_eq_left h, max_eq_left (fx_le_iff.2 h)]

lemma fx_le_zero_iff {a : ℤ} : fx a ≤ 0 ↔ a ≤ 0 := by rw [← fx_zeroC, fx_le_iff]

lemma fx_two_mul (a : ℤ) : fx (2 * a) = 2 * fx a := by unfold fx; push_cast; ring

lemma mem_one : ivMem (1 : ℝ) (Iv.int 1) := by simpa using Iv.mem_int 1

lemma mem_zero : ivMem (0 : ℝ) (Iv.int 0) := by simpa using Iv.mem_int 0

lemma mem_unit {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : ivMem x ⟨0, ONE⟩ := by
  unfold ivMem
  simp only [Int.cast_zero, ONE_cast]
  exact ⟨mul_nonneg h0 SC_pos.le, by nlinarith [SC_pos]⟩

/-- the clamped ratio branch of `cdfIv` -/
lemma clamp_mem (t w : ℤ) (hw : 0 < w) :
    ivMem (min (max (fx t / fx w) 0) 1)
      (if t ≤ 0 then Iv.int 0 else if w ≤ t then Iv.int 1 else Iv.div (Iv.pt t) (Iv.pt w)) := by
  have hfw : 0 < fx w := fx_pos_iff.2 hw
  split_ifs with h1 h2
  · have : fx t / fx w ≤ 0 := div_nonpos_of_nonpos_of_nonneg (fx_le_zero_iff.2 h1) hfw.le
    rw [max_eq_right this, min_eq_left zero_le_one]; exact mem_zero
  · have : 1 ≤ fx t / fx w := (one_le_div hfw).2 (fx_le_iff.2 h2)
    rw [max_eq_left (zero_le_one.trans this), min_eq_right this]; exact mem_one
  · push Not at h1 h2
    have hpos : 0 < fx t / fx w := div_pos (fx_pos_iff.2 h1) hfw
    have hlt : fx t / fx w < 1 := (div_lt_one hfw).2 (fx_lt_iff.2 h2)
    rw [max_eq_left hpos.le, min_eq_left hlt.le]
    exact Iv.mem_div (Iv.mem_pt t) (Iv.mem_pt w) (by simpa [Iv.pt] using hw)

/-! ## `CdfIvProp` -/

lemma cdfIv_proper (a b c d z : ℤ) (hab : a < b) (hcd : c < d) :
    ivMem (cdfR (fx a) (fx b) (fx c) (fx d) (fx z)) (cdfIv a b c d z) := by
  have hw1 : b - a ≠ 0 := by omega
  have hw2 : d - c ≠ 0 := by omega
  have hab' : fx a < fx b := fx_lt_iff.2 hab
  have hcd' : fx c < fx d := fx_lt_iff.2 hcd
  have h01 := cdfR_mem01 hab'.le hcd'.le (fx z)
  rw [cdfR_piece hab' hcd']
  have hU : fx z + fx d - fx a = fx (d - a + z) := by rw [fx_add, fx_subC]; ring
  have hP : min (fx b - fx a) (fx d - fx c) = fx (min (b - a) (d - c)) := by rw [fx_min, fx_subC, fx_subC]
  have hQ : max (fx b - fx a) (fx d - fx c) = fx (max (b - a) (d - c)) := by rw [fx_maxC, fx_subC, fx_subC]
  rw [cdfR_piece hab' hcd', hU, hP, hQ] at h01
  rw [hU, hP, hQ]
  simp only [cdfIv, beq_iff_eq, hw1, hw2, false_and, or_self, ↓reduceIte]
  set p := min (b - a) (d - c) with hpdef
  set q := max (b - a) (d - c) with hqdef
  set u := d - a + z with hudef
  have hp : 0 < p := lt_min (by omega) (by omega)
  have hpq : p ≤ q := min_le_max
  have hq : 0 < q := hp.trans_le hpq
  have hfp : 0 < fx p := fx_pos_iff.2 hp
  have hfq : 0 < fx q := fx_pos_iff.2 hq
  have hpq' : fx p + fx q = fx (p + q) := (fx_add p q).symm
  have hden : ivMem (fx p * fx q * ((2 : ℕ) : ℝ)) (Iv.mulNat (Iv.mul (Iv.pt p) (Iv.pt q)) 2) :=
    Iv.mem_mulNat (Iv.mem_mul (Iv.mem_pt p) (Iv.mem_pt q)) 2
  simp only [fx_le_zero_iff, fx_le_iff, hpq'] at h01 ⊢
  by_cases c1 : u ≤ 0
  · simp only [c1, ↓reduceIte]; exact mem_zero
  simp only [c1, ↓reduceIte] at h01 ⊢
  by_cases c2 : p + q ≤ u
  · simp only [c2, ↓reduceIte]
    have n1 : ¬ u ≤ p := by omega
    have n2 : ¬ u ≤ q := by omega
    simp only [n1, n2, ↓reduceIte]
    split_ifs with c3
    · have : u = p + q := by omega
      rw [this, ← hpq', sub_self]; simpa using mem_one
    · exact mem_one
  simp only [c2, ↓reduceIte, show ¬ p ≤ 0 by omega]
  by_cases c3 : (Iv.mulNat (Iv.mul (Iv.pt p) (Iv.pt q)) 2).lo ≤ 0
  · simp only [c3, ↓reduceIte]; exact mem_unit h01.1 h01.2
  simp only [c3, ↓reduceIte]
  push Not at c3
  have hden' : ivMem (2 * fx p * fx q) (Iv.mulNat (Iv.mul (Iv.pt p) (Iv.pt q)) 2) := by
    convert hden using 1; push_cast; ring
  by_cases c4 : u ≤ p
  · simp only [c4, ↓reduceIte]
    exact Iv.mem_div (Iv.mem_sqr (Iv.mem_pt u)) hden' c3
  simp only [c4, ↓reduceIte]
  by_cases c5 : u ≤ q
  · simp only [c5, ↓reduceIte]
    have h2 := Iv.mem_div (Iv.mem_pt (2 * u - p)) (Iv.mem_pt (2 * q)) (by simp [Iv.pt]; omega)
    convert h2 using 1
    rw [fx_subC, fx_two_mul, fx_two_mul]
  have c6 : u ≤ p + q := by omega
  simp only [c5, c6, ↓reduceIte]
  have h2 := Iv.mem_sub mem_one (Iv.mem_div (Iv.mem_sqr (Iv.mem_pt (p + q - u))) hden' c3)
  convert h2 using 1
  rw [fx_subC]

theorem cdfIvProp : CdfIvProp := by
  intro a b c d z hab hcd
  rcases eq_or_lt_of_le hab with hab' | hab' <;> rcases eq_or_lt_of_le hcd with hcd' | hcd'
  · -- both point masses
    subst hab' hcd'
    simp only [cdfIv, sub_self, beq_self_eq_true, and_self, ↓reduceIte, cdfR]
    rw [← fx_subC]
    simp only [fx_le_iff]
    split_ifs
    · exact mem_one
    · exact mem_zero
  · -- `X` a point mass
    subst hab'
    have hw2 : d - c ≠ 0 := by omega
    have hcd'' : fx c ≠ fx d := (fx_lt_iff.2 hcd').ne
    simp only [cdfIv, sub_self, beq_self_eq_true, beq_iff_eq, hw2, and_false, true_or, ↓reduceIte,
      cdfR, hcd'', and_false]
    have e : (fx z + fx d - fx a) / (fx d - fx c) = fx (d - a + z) / fx (d - c) := by
      rw [fx_add, fx_subC, fx_subC]; ring_nf
    rw [e]
    exact clamp_mem (d - a + z) (d - c) (by omega)
  · -- `Y` a point mass
    subst hcd'
    have hw1 : b - a ≠ 0 := by omega
    have hab'' : fx a ≠ fx b := (fx_lt_iff.2 hab').ne
    simp only [cdfIv, sub_self, beq_self_eq_true, beq_iff_eq, hw1, or_true,
      ↓reduceIte, cdfR, hab'', and_true]
    have e : (fx z + fx c - fx a) / (fx b - fx a) = fx (c - a + z) / fx (b - a) := by
      rw [fx_add, fx_subC, fx_subC]; ring_nf
    rw [e]
    exact clamp_mem (c - a + z) (b - a) (by omega)
  · exact cdfIv_proper a b c d z hab' hcd'

end BHH
