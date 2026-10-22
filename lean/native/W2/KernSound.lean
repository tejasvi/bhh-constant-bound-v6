/-
Soundness of the kernels of the production recursion: `kern1` (`e^{-ā 2^-dtl}`), `powFix` (powers with directed
rounding), `kernFromE1` (`e^{-t ā}` at scale `2^-62`) and `kern` (first-step kernels).
-/
import W2.FixSound
import W2.RecArith

open Real

namespace BHH.W2

open W2C BHH.Cert BHH

lemma toNat_cast_le_of_le {a : ℤ} {x : ℝ} (h : (a : ℝ) ≤ x) (hx : 0 ≤ x) : ((a.toNat : ℕ) : ℝ) ≤ x := by
  rcases le_total a 0 with ha | ha
  · rw [Int.toNat_of_nonpos ha]; simpa using hx
  · have : ((a.toNat : ℕ) : ℝ) = (a : ℝ) := by rw [← Int.cast_natCast, Int.toNat_of_nonneg ha]
    rw [this]; exact h

lemma le_toNat_cast {a : ℤ} {x : ℝ} (h : x ≤ (a : ℝ)) : x ≤ ((a.toNat : ℕ) : ℝ) := by
  have : (a : ℝ) ≤ ((a.toNat : ℕ) : ℝ) := by
    have h1 := Int.self_le_toNat a
    exact_mod_cast h1
  linarith

/-- `powFix true x j ≤ 2^PR (x / 2^PR)^j`. -/
theorem powFix_lower (x : ℕ) : ∀ j, (powFix true x j : ℝ) ≤ 2 ^ PR * ((x : ℝ) / 2 ^ PR) ^ j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases j with _ | j
    · simp [powFix]
    · rw [powFix]
      simp only [ite_true]
      have hP : (0 : ℝ) < 2 ^ PR := by positivity
      set m := (j + 1) / 2 with hm
      set h := powFix true x m
      have ihm := ih m (by omega)
      have hy : (0 : ℝ) ≤ (x : ℝ) / 2 ^ PR := by positivity
      have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg _
      -- h2 := (h * h) >>> PR ≤ 2^PR y^(2m)
      have hh2 : (((h * h) >>> PR : ℕ) : ℝ) ≤ 2 ^ PR * ((x : ℝ) / 2 ^ PR) ^ (2 * m) := by
        rw [Nat.shiftRight_eq_div_pow]
        have a1 : (((h * h) / 2 ^ PR : ℕ) : ℝ) ≤ ((h * h : ℕ) : ℝ) / 2 ^ PR := by
          have := Nat.div_mul_le_self (h * h) (2 ^ PR)
          rw [le_div_iff₀ hP]; exact_mod_cast this
        have a2 : ((h * h : ℕ) : ℝ) ≤ (2 ^ PR * ((x : ℝ) / 2 ^ PR) ^ m) ^ 2 := by
          push_cast; rw [← sq]; exact pow_le_pow_left₀ hh0 ihm 2
        calc _ ≤ ((h * h : ℕ) : ℝ) / 2 ^ PR := a1
          _ ≤ (2 ^ PR * ((x : ℝ) / 2 ^ PR) ^ m) ^ 2 / 2 ^ PR := by gcongr
          _ = 2 ^ PR * ((x : ℝ) / 2 ^ PR) ^ (2 * m) := by field_simp; ring
      by_cases hev : (j + 1) % 2 = 0
      · have e : 2 * m = j + 1 := by omega
        simp only [show ((j + 1) % 2 == 0) = true by simp [hev], ite_true]
        rw [← e]; exact hh2
      · have e : 2 * m + 1 = j + 1 := by omega
        simp only [show ((j + 1) % 2 == 0) = false by simp [hev], Bool.false_eq_true, ite_false]
        rw [Nat.shiftRight_eq_div_pow, ← e]
        have a1 : ((((h * h) >>> PR) * x / 2 ^ PR : ℕ) : ℝ) ≤ ((((h * h) >>> PR) * x : ℕ) : ℝ) / 2 ^ PR := by
          have := Nat.div_mul_le_self (((h * h) >>> PR) * x) (2 ^ PR)
          rw [le_div_iff₀ hP]; exact_mod_cast this
        calc _ ≤ ((((h * h) >>> PR) * x : ℕ) : ℝ) / 2 ^ PR := a1
          _ = (((h * h) >>> PR : ℕ) : ℝ) * ((x : ℝ) / 2 ^ PR) := by push_cast; ring
          _ ≤ (2 ^ PR * ((x : ℝ) / 2 ^ PR) ^ (2 * m)) * ((x : ℝ) / 2 ^ PR) := by gcongr
          _ = 2 ^ PR * ((x : ℝ) / 2 ^ PR) ^ (2 * m + 1) := by ring

/-- `2^PR (x / 2^PR)^j ≤ powFix false x j`. -/
theorem powFix_upper (x : ℕ) : ∀ j, 2 ^ PR * ((x : ℝ) / 2 ^ PR) ^ j ≤ (powFix false x j : ℝ) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases j with _ | j
    · simp [powFix]
    · rw [powFix]
      simp only [Bool.false_eq_true, ite_false]
      have hP : (0 : ℝ) < 2 ^ PR := by positivity
      set m := (j + 1) / 2 with hm
      set h := powFix false x m
      have ihm := ih m (by omega)
      have hy : (0 : ℝ) ≤ (x : ℝ) / 2 ^ PR := by positivity
      have hceil : ∀ v : ℕ, (v : ℝ) / 2 ^ PR ≤ (((v + 2 ^ PR - 1) >>> PR : ℕ) : ℝ) := by
        intro v
        rw [Nat.shiftRight_eq_div_pow, div_le_iff₀ hP]
        have := nat_le_ceil_mul v (2 ^ PR) Nat.one_le_two_pow
        rw [show v + 2 ^ PR - 1 = v + (2 ^ PR - 1) by have := Nat.one_le_two_pow (n := PR); omega]
        exact_mod_cast this
      have hh2 : 2 ^ PR * ((x : ℝ) / 2 ^ PR) ^ (2 * m) ≤ (((h * h + 2 ^ PR - 1) >>> PR : ℕ) : ℝ) := by
        have hlhs0 : (0 : ℝ) ≤ 2 ^ PR * ((x : ℝ) / 2 ^ PR) ^ m :=
          mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg hy m)
        have a2 : (2 ^ PR * ((x : ℝ) / 2 ^ PR) ^ m) ^ 2 ≤ ((h * h : ℕ) : ℝ) := by
          push_cast; rw [← sq]; exact pow_le_pow_left₀ hlhs0 ihm 2
        calc 2 ^ PR * ((x : ℝ) / 2 ^ PR) ^ (2 * m) = (2 ^ PR * ((x : ℝ) / 2 ^ PR) ^ m) ^ 2 / 2 ^ PR := by
              field_simp; ring
          _ ≤ ((h * h : ℕ) : ℝ) / 2 ^ PR := by gcongr
          _ ≤ _ := hceil (h * h)
      by_cases hev : (j + 1) % 2 = 0
      · have e : 2 * m = j + 1 := by omega
        simp only [show ((j + 1) % 2 == 0) = true by simp [hev], ite_true]
        rw [← e]; exact hh2
      · have e : 2 * m + 1 = j + 1 := by omega
        simp only [show ((j + 1) % 2 == 0) = false by simp [hev], Bool.false_eq_true, ite_false]
        rw [← e]
        calc 2 ^ PR * ((x : ℝ) / 2 ^ PR) ^ (2 * m + 1)
            = (2 ^ PR * ((x : ℝ) / 2 ^ PR) ^ (2 * m)) * ((x : ℝ) / 2 ^ PR) := by ring
          _ ≤ (((h * h + 2 ^ PR - 1) >>> PR : ℕ) : ℝ) * ((x : ℝ) / 2 ^ PR) := by gcongr
          _ = ((((h * h + 2 ^ PR - 1) >>> PR) * x : ℕ) : ℝ) / 2 ^ PR := by push_cast; ring
          _ ≤ _ := hceil _

lemma div_two_pow_cast {a : ℤ} {q : ℕ} (hd : (2 : ℤ) ^ q ∣ a) : ((a / 2 ^ q : ℤ) : ℝ) = (a : ℝ) / 2 ^ q := by
  obtain ⟨b, rfl⟩ := hd
  rw [Int.mul_ediv_cancel_left _ (by positivity)]
  push_cast; field_simp

lemma fx_div_two_pow {a : ℤ} {q : ℕ} (hd : (2 : ℤ) ^ q ∣ a) : fx (a / 2 ^ q) = fx a / 2 ^ q := by
  unfold fx; rw [div_two_pow_cast hd]; ring

lemma fx_eq' (n : ℤ) : (n : ℝ) = fx n * 2 ^ PR := by unfold fx; field_simp

/-- `kern1 true dtl a ≤ 2^PR e^{-fx(a)/2^dtl}`. -/
theorem kern1_lower (dtl : ℕ) (a : ℤ) (hd : (2 : ℤ) ^ dtl ∣ a) :
    (kern1 true dtl a : ℝ) ≤ 2 ^ PR * Real.exp (-(fx a / 2 ^ dtl)) := by
  unfold kern1; simp only [ite_true]
  have h := expPt_lo (-(a / 2 ^ dtl))
  have e : fx (-(a / 2 ^ dtl)) = -(fx a / 2 ^ dtl) := by rw [fx_neg, fx_div_two_pow hd]
  rw [e] at h
  apply toNat_cast_le_of_le _ (by positivity)
  rw [fx_eq' (W2C.expPt (-(a / 2 ^ dtl))).lo]
  have hP : (0 : ℝ) < 2 ^ PR := by positivity
  nlinarith

/-- `2^PR e^{-fx(a)/2^dtl} ≤ kern1 false dtl a` (for `a ≥ 0`). -/
theorem kern1_upper (dtl : ℕ) (a : ℤ) (hd : (2 : ℤ) ^ dtl ∣ a) (ha : 0 ≤ a) :
    2 ^ PR * Real.exp (-(fx a / 2 ^ dtl)) ≤ (kern1 false dtl a : ℝ) := by
  unfold kern1; simp only [Bool.false_eq_true, ite_false]
  have hneg : -(a / 2 ^ dtl) ≤ 0 := by
    have : 0 ≤ a / 2 ^ dtl := Int.ediv_nonneg ha (by positivity)
    omega
  have h := expPt_hi (-(a / 2 ^ dtl)) (Or.inr hneg)
  have e : fx (-(a / 2 ^ dtl)) = -(fx a / 2 ^ dtl) := by rw [fx_neg, fx_div_two_pow hd]
  rw [e] at h
  apply le_toNat_cast
  rw [fx_eq' (W2C.expPt (-(a / 2 ^ dtl))).hi]
  have hP : (0 : ℝ) < 2 ^ PR := by positivity
  nlinarith

/-- `kernFromE1 true j x ≤ 2^62 Y^j` if `x ≤ 2^PR Y`. -/
theorem kernFromE1_lower (j x : ℕ) {Y : ℝ} (hx : (x : ℝ) ≤ 2 ^ PR * Y) :
    (kernFromE1 true j x : ℝ) ≤ 2 ^ 62 * Y ^ j := by
  unfold kernFromE1; simp only [ite_true]
  rw [Nat.shiftRight_eq_div_pow]
  have hP : (0 : ℝ) < 2 ^ (PR - 62) := by positivity
  have a1 : ((powFix true x j / 2 ^ (PR - 62) : ℕ) : ℝ) ≤ (powFix true x j : ℝ) / 2 ^ (PR - 62) := by
    have := Nat.div_mul_le_self (powFix true x j) (2 ^ (PR - 62))
    rw [le_div_iff₀ hP]; exact_mod_cast this
  have a2 := powFix_lower x j
  have hy : (0 : ℝ) ≤ (x : ℝ) / 2 ^ PR := by positivity
  have hyY : (x : ℝ) / 2 ^ PR ≤ Y := by rw [div_le_iff₀ (by positivity)]; linarith
  have ePR : (2 : ℝ) ^ PR = 2 ^ 62 * 2 ^ (PR - 62) := by rw [← pow_add]; congr 1
  calc _ ≤ (powFix true x j : ℝ) / 2 ^ (PR - 62) := a1
    _ ≤ 2 ^ PR * ((x : ℝ) / 2 ^ PR) ^ j / 2 ^ (PR - 62) := by gcongr
    _ = 2 ^ 62 * ((x : ℝ) / 2 ^ PR) ^ j := by rw [ePR]; field_simp
    _ ≤ 2 ^ 62 * Y ^ j := by gcongr

/-- `2^62 Y^j ≤ kernFromE1 false j x` if `2^PR Y ≤ x`, `Y ≥ 0`. -/
theorem kernFromE1_upper (j x : ℕ) {Y : ℝ} (hY : 0 ≤ Y) (hx : 2 ^ PR * Y ≤ (x : ℝ)) :
    2 ^ 62 * Y ^ j ≤ (kernFromE1 false j x : ℝ) := by
  unfold kernFromE1; simp only [Bool.false_eq_true, ite_false]
  rw [Nat.shiftRight_eq_div_pow]
  have hP : (0 : ℝ) < 2 ^ (PR - 62) := by positivity
  have a1 : (powFix false x j : ℝ) / 2 ^ (PR - 62) ≤
      (((powFix false x j + 2 ^ (PR - 62) - 1) / 2 ^ (PR - 62) : ℕ) : ℝ) := by
    rw [div_le_iff₀ hP]
    have := nat_le_ceil_mul (powFix false x j) (2 ^ (PR - 62)) Nat.one_le_two_pow
    rw [show powFix false x j + 2 ^ (PR - 62) - 1 = powFix false x j + (2 ^ (PR - 62) - 1) by
      have := Nat.one_le_two_pow (n := PR - 62); omega]
    exact_mod_cast this
  have a2 := powFix_upper x j
  have hyY : Y ≤ (x : ℝ) / 2 ^ PR := by rw [le_div_iff₀ (by positivity)]; linarith
  have ePR : (2 : ℝ) ^ PR = 2 ^ 62 * 2 ^ (PR - 62) := by rw [← pow_add]; congr 1
  calc 2 ^ 62 * Y ^ j ≤ 2 ^ 62 * ((x : ℝ) / 2 ^ PR) ^ j := by gcongr
    _ = 2 ^ PR * ((x : ℝ) / 2 ^ PR) ^ j / 2 ^ (PR - 62) := by rw [ePR]; field_simp
    _ ≤ (powFix false x j : ℝ) / 2 ^ (PR - 62) := by gcongr
    _ ≤ _ := a1

/-- First-step kernels: `kern true j dtl a ≤ 2^62 e^{-(j/2^dtl) fx(a)}`. -/
theorem kern_lower (j dtl : ℕ) (a : ℤ) (hd : (2 : ℤ) ^ dtl ∣ a) :
    (kern true j dtl a : ℝ) ≤ 2 ^ 62 * Real.exp (-((j : ℝ) / 2 ^ dtl * fx a)) := by
  unfold kern; simp only [ite_true]
  have hd' : (2 : ℤ) ^ dtl ∣ (j : ℤ) * a := Dvd.dvd.mul_left hd _
  have e : fx (-((j : ℤ) * a / 2 ^ dtl)) = -((j : ℝ) / 2 ^ dtl * fx a) := by
    rw [fx_neg, fx_div_two_pow hd']; unfold fx; push_cast; ring
  have h := expPt_lo (-((j : ℤ) * a / 2 ^ dtl))
  rw [e] at h
  apply toNat_cast_le_of_le _ (by positivity)
  have hs := shrD_le (W2C.expPt (-((j : ℤ) * a / 2 ^ dtl))).lo (PR - 62)
  have hP : (0 : ℝ) < 2 ^ (PR - 62) := by positivity
  have ePR : (2 : ℝ) ^ PR = 2 ^ 62 * 2 ^ (PR - 62) := by rw [← pow_add]; congr 1
  have hlo : ((W2C.expPt (-((j : ℤ) * a / 2 ^ dtl))).lo : ℝ) ≤ 2 ^ PR * Real.exp (-((j : ℝ) / 2 ^ dtl * fx a)) := by
    rw [fx_eq' (W2C.expPt (-((j : ℤ) * a / 2 ^ dtl))).lo]
    have : (0 : ℝ) < 2 ^ PR := by positivity
    nlinarith
  calc _ ≤ ((W2C.expPt (-((j : ℤ) * a / 2 ^ dtl))).lo : ℝ) / 2 ^ (PR - 62) := hs
    _ ≤ 2 ^ PR * Real.exp (-((j : ℝ) / 2 ^ dtl * fx a)) / 2 ^ (PR - 62) := by gcongr
    _ = 2 ^ 62 * Real.exp (-((j : ℝ) / 2 ^ dtl * fx a)) := by rw [ePR]; field_simp

/-- First-step kernels: `2^62 e^{-(j/2^dtl) fx(a)} ≤ kern false j dtl a` (for `a ≥ 0`). -/
theorem kern_upper (j dtl : ℕ) (a : ℤ) (hd : (2 : ℤ) ^ dtl ∣ a) (ha : 0 ≤ a) :
    2 ^ 62 * Real.exp (-((j : ℝ) / 2 ^ dtl * fx a)) ≤ (kern false j dtl a : ℝ) := by
  unfold kern; simp only [Bool.false_eq_true, ite_false]
  have hd' : (2 : ℤ) ^ dtl ∣ (j : ℤ) * a := Dvd.dvd.mul_left hd _
  have e : fx (-((j : ℤ) * a / 2 ^ dtl)) = -((j : ℝ) / 2 ^ dtl * fx a) := by
    rw [fx_neg, fx_div_two_pow hd']; unfold fx; push_cast; ring
  have hneg : -((j : ℤ) * a / 2 ^ dtl) ≤ 0 := by
    have : 0 ≤ (j : ℤ) * a / 2 ^ dtl := Int.ediv_nonneg (mul_nonneg (by positivity) ha) (by positivity)
    omega
  have h := expPt_hi (-((j : ℤ) * a / 2 ^ dtl)) (Or.inr hneg)
  rw [e] at h
  apply le_toNat_cast
  have hs := le_shrU (W2C.expPt (-((j : ℤ) * a / 2 ^ dtl))).hi (PR - 62)
  have hP : (0 : ℝ) < 2 ^ (PR - 62) := by positivity
  have ePR : (2 : ℝ) ^ PR = 2 ^ 62 * 2 ^ (PR - 62) := by rw [← pow_add]; congr 1
  have hhi : 2 ^ PR * Real.exp (-((j : ℝ) / 2 ^ dtl * fx a)) ≤ ((W2C.expPt (-((j : ℤ) * a / 2 ^ dtl))).hi : ℝ) := by
    rw [fx_eq' (W2C.expPt (-((j : ℤ) * a / 2 ^ dtl))).hi]
    have : (0 : ℝ) < 2 ^ PR := by positivity
    nlinarith
  calc 2 ^ 62 * Real.exp (-((j : ℝ) / 2 ^ dtl * fx a))
      = 2 ^ PR * Real.exp (-((j : ℝ) / 2 ^ dtl * fx a)) / 2 ^ (PR - 62) := by rw [ePR]; field_simp
    _ ≤ ((W2C.expPt (-((j : ℤ) * a / 2 ^ dtl))).hi : ℝ) / 2 ^ (PR - 62) := by gcongr
    _ ≤ _ := hs

end BHH.W2
