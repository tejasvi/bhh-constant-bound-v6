/-
Soundness of the fixed-point interval arithmetic of `BHHCert/Exact.lean` (module A).

`ivMem x a` (from `BHH/Interfaces.lean`) means `a.lo ≤ x · 2^PR ≤ a.hi`, i.e. `x ∈ [a.lo / 2^PR, a.hi / 2^PR]`.
-/
import Mathlib
import BHH.Interfaces

open BHH.Cert

namespace BHH

/-- the scale `2^PR` as a real number -/
noncomputable abbrev SC : ℝ := (2 : ℝ) ^ PR

lemma SC_pos : (0 : ℝ) < SC := by positivity

lemma ONE_cast : ((ONE : ℤ) : ℝ) = SC := by
  simp only [ONE, SC, PR]; norm_num

lemma fx_eq (n : ℤ) : fx n = (n : ℝ) / SC := rfl

/-! ## shifts and divisions -/

lemma shrD_le (a : ℤ) (n : ℕ) : ((shrD a n : ℤ) : ℝ) ≤ (a : ℝ) / 2 ^ n := by
  unfold shrD
  rw [Int.shiftRight_eq_div_pow]
  have h2 : (0 : ℤ) < 2 ^ n := by positivity
  rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 ^ n)]
  have := Int.ediv_mul_le a (ne_of_gt h2)
  exact_mod_cast this

lemma le_shrU (a : ℤ) (n : ℕ) : (a : ℝ) / 2 ^ n ≤ ((shrU a n : ℤ) : ℝ) := by
  have h := shrD_le (-a) n
  unfold shrD at h
  unfold shrU
  rw [Int.cast_neg]
  push_cast at h
  rw [neg_div] at h
  linarith

lemma divD_le (a b : ℤ) (hb : 0 < b) : ((divD a b : ℤ) : ℝ) ≤ (a : ℝ) / b := by
  unfold divD
  rw [le_div_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast Int.ediv_mul_le a (ne_of_gt hb)

lemma le_divU (a b : ℤ) (hb : 0 < b) : (a : ℝ) / b ≤ ((divU a b : ℤ) : ℝ) := by
  have h := divD_le (-a) b hb
  unfold divD at h
  unfold divU
  rw [Int.cast_neg]
  push_cast at h
  rw [neg_div] at h
  linarith

/-! ## basic operations -/

namespace Cert.Iv

lemma mem_pt (n : ℤ) : ivMem (fx n) (pt n) := by
  unfold ivMem pt fx; simp [div_mul_cancel₀ _ (ne_of_gt SC_pos)]

lemma mem_int (n : ℤ) : ivMem (n : ℝ) (int n) := by
  unfold ivMem int; push_cast; rw [ONE_cast]; simp

lemma mem_add {x y : ℝ} {a b : Iv} (hx : ivMem x a) (hy : ivMem y b) : ivMem (x + y) (add a b) := by
  unfold ivMem add at *; push_cast; constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]

lemma mem_sub {x y : ℝ} {a b : Iv} (hx : ivMem x a) (hy : ivMem y b) : ivMem (x - y) (sub a b) := by
  unfold ivMem sub at *; push_cast; constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]

lemma mem_neg {x : ℝ} {a : Iv} (hx : ivMem x a) : ivMem (-x) (neg a) := by
  unfold ivMem neg at *; push_cast; constructor <;> nlinarith [hx.1, hx.2]

lemma mem_widen {x : ℝ} {a : Iv} (hx : ivMem x a) {e : ℤ} (he : 0 ≤ e) : ivMem x (widen a e) := by
  unfold ivMem widen at *; push_cast
  have : (0:ℝ) ≤ e := by exact_mod_cast he
  constructor <;> linarith [hx.1, hx.2]

lemma mem_hull_left {x : ℝ} {a b : Iv} (hx : ivMem x a) : ivMem x (hull a b) := by
  unfold ivMem hull at *; push_cast
  exact ⟨le_trans (min_le_left _ _) hx.1, le_trans hx.2 (le_max_left _ _)⟩

lemma mem_hull_right {x : ℝ} {a b : Iv} (hx : ivMem x b) : ivMem x (hull a b) := by
  unfold ivMem hull at *; push_cast
  exact ⟨le_trans (min_le_right _ _) hx.1, le_trans hx.2 (le_max_right _ _)⟩

lemma mem_mulNat {x : ℝ} {a : Iv} (hx : ivMem x a) (n : ℕ) : ivMem (x * n) (mulNat a n) := by
  unfold ivMem mulNat at *; push_cast
  have hn : (0:ℝ) ≤ n := by positivity
  constructor <;> nlinarith [hx.1, hx.2]

lemma mem_divNat {x : ℝ} {a : Iv} (hx : ivMem x a) {n : ℕ} (hn : 0 < n) : ivMem (x / n) (divNat a n) := by
  unfold ivMem divNat at *
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have h1 := divD_le a.lo n (by exact_mod_cast hn)
  have h2 := le_divU a.hi n (by exact_mod_cast hn)
  push_cast at h1 h2
  constructor
  · calc ((divD a.lo n : ℤ) : ℝ) ≤ (a.lo : ℝ) / n := h1
      _ ≤ x * SC / n := by gcongr; exact hx.1
      _ = x / n * SC := by ring
  · calc x / n * SC = x * SC / n := by ring
      _ ≤ (a.hi : ℝ) / n := by gcongr; exact hx.2
      _ ≤ _ := h2

lemma mem_div2e {x : ℝ} {a : Iv} (hx : ivMem x a) (e : ℕ) : ivMem (x / 2 ^ e) (div2e a e) := by
  unfold ivMem div2e at *
  have h1 := shrD_le a.lo e
  have h2 := le_shrU a.hi e
  have he : (0:ℝ) < 2 ^ e := by positivity
  constructor
  · calc ((shrD a.lo e : ℤ) : ℝ) ≤ (a.lo : ℝ) / 2 ^ e := h1
      _ ≤ x * SC / 2 ^ e := by gcongr; exact hx.1
      _ = x / 2 ^ e * SC := by ring
  · calc x / 2 ^ e * SC = x * SC / 2 ^ e := by ring
      _ ≤ (a.hi : ℝ) / 2 ^ e := by gcongr; exact hx.2
      _ ≤ _ := h2

lemma mem_mul2e {x : ℝ} {a : Iv} (hx : ivMem x a) (e : ℕ) : ivMem (x * 2 ^ e) (mul2e a e) := by
  unfold ivMem mul2e at *; push_cast
  have he : (0:ℝ) < 2 ^ e := by positivity
  constructor <;> nlinarith [hx.1, hx.2]

/-- the product rounding step: if `P ≤ X·Y ≤ Q` for the scaled values `X = x·2^PR`, `Y = y·2^PR`, then
`x·y ∈ [shrD P PR, shrU Q PR]` -/
lemma mem_of_prod {x y : ℝ} {P Q : ℤ} (hP : (P : ℝ) ≤ (x * SC) * (y * SC))
    (hQ : (x * SC) * (y * SC) ≤ (Q : ℝ)) : ivMem (x * y) ⟨shrD P PR, shrU Q PR⟩ := by
  unfold ivMem
  have h1 := shrD_le P PR
  have h2 := le_shrU Q PR
  have hS : (2:ℝ) ^ PR = SC := rfl
  rw [hS] at h1 h2
  have e : x * y * SC = (x * SC) * (y * SC) / SC := by field_simp
  constructor
  · simp only; rw [e]; calc ((shrD P PR : ℤ) : ℝ) ≤ (P : ℝ) / SC := h1
      _ ≤ _ := by gcongr
  · simp only; rw [e]; calc (x * SC) * (y * SC) / SC ≤ (Q : ℝ) / SC := by gcongr
      _ ≤ _ := h2

/-- rounding step with the products in generalized form -/
lemma mem_of_prod' {x y : ℝ} {P Q : ℤ}
    (h : ∀ X Y : ℝ, X = x * SC → Y = y * SC → (P : ℝ) ≤ X * Y ∧ X * Y ≤ (Q : ℝ)) :
    ivMem (x * y) ⟨shrD P PR, shrU Q PR⟩ :=
  mem_of_prod (h _ _ rfl rfl).1 (h _ _ rfl rfl).2

lemma mem_mul {x y : ℝ} {a b : Iv} (hx : ivMem x a) (hy : ivMem y b) : ivMem (x * y) (mul a b) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  unfold mul
  split_ifs with ha hb1 hb2 ha2 hb3 hb4 hb5 hb6
  all_goals
    refine mem_of_prod' fun X Y hX hY => ?_
    rw [← hX] at h1 h2
    rw [← hY] at h3 h4
    push_cast
  · have : (0:ℝ) ≤ a.lo := by exact_mod_cast ha
    have : (0:ℝ) ≤ b.lo := by exact_mod_cast hb1
    constructor <;> nlinarith
  · have : (0:ℝ) ≤ a.lo := by exact_mod_cast ha
    have : (b.hi:ℝ) ≤ 0 := by exact_mod_cast hb2
    constructor <;> nlinarith
  · have : (0:ℝ) ≤ a.lo := by exact_mod_cast ha
    have : (b.lo:ℝ) < 0 := by exact_mod_cast (lt_of_not_ge hb1)
    have : (0:ℝ) < b.hi := by exact_mod_cast (lt_of_not_ge hb2)
    constructor <;> nlinarith
  · have : (a.hi:ℝ) ≤ 0 := by exact_mod_cast ha2
    have : (0:ℝ) ≤ b.lo := by exact_mod_cast hb3
    constructor <;> nlinarith
  · have : (a.hi:ℝ) ≤ 0 := by exact_mod_cast ha2
    have : (b.hi:ℝ) ≤ 0 := by exact_mod_cast hb4
    constructor <;> nlinarith
  · have : (a.hi:ℝ) ≤ 0 := by exact_mod_cast ha2
    have : (b.lo:ℝ) < 0 := by exact_mod_cast (lt_of_not_ge hb3)
    have : (0:ℝ) < b.hi := by exact_mod_cast (lt_of_not_ge hb4)
    constructor <;> nlinarith
  · have : (a.lo:ℝ) < 0 := by exact_mod_cast (lt_of_not_ge ha)
    have : (0:ℝ) < a.hi := by exact_mod_cast (lt_of_not_ge ha2)
    have : (0:ℝ) ≤ b.lo := by exact_mod_cast hb5
    constructor <;> nlinarith
  · have : (a.lo:ℝ) < 0 := by exact_mod_cast (lt_of_not_ge ha)
    have : (0:ℝ) < a.hi := by exact_mod_cast (lt_of_not_ge ha2)
    have : (b.hi:ℝ) ≤ 0 := by exact_mod_cast hb6
    constructor <;> nlinarith
  · have : (a.lo:ℝ) < 0 := by exact_mod_cast (lt_of_not_ge ha)
    have : (0:ℝ) < a.hi := by exact_mod_cast (lt_of_not_ge ha2)
    have : (b.lo:ℝ) < 0 := by exact_mod_cast (lt_of_not_ge hb5)
    have : (0:ℝ) < b.hi := by exact_mod_cast (lt_of_not_ge hb6)
    constructor
    · rcases le_total 0 Y with hY0 | hY0
      · exact le_trans (min_le_left _ _) (by nlinarith)
      · exact le_trans (min_le_right _ _) (by nlinarith)
    · rcases le_total 0 Y with hY0 | hY0
      · exact le_trans (by nlinarith) (le_max_right _ _)
      · exact le_trans (by nlinarith) (le_max_left _ _)

lemma mem_sqr {x : ℝ} {a : Iv} (hx : ivMem x a) : ivMem (x ^ 2) (sqr a) := by
  obtain ⟨h1, h2⟩ := hx
  rw [sq]
  unfold sqr
  split_ifs with ha hb
  · refine mem_of_prod' fun X Y hX hY => ?_
    have hXY : X = Y := by rw [hX, hY]
    rw [← hX] at h1 h2
    subst hXY
    push_cast
    have : (0:ℝ) ≤ a.lo := by exact_mod_cast ha
    constructor <;> nlinarith
  · refine mem_of_prod' fun X Y hX hY => ?_
    have hXY : X = Y := by rw [hX, hY]
    rw [← hX] at h1 h2
    subst hXY
    push_cast
    have : (a.hi:ℝ) ≤ 0 := by exact_mod_cast hb
    constructor <;> nlinarith
  · unfold ivMem
    have h2' := le_shrU (Max.max (a.lo * a.lo) (a.hi * a.hi)) PR
    have hS : (2:ℝ) ^ PR = SC := rfl
    rw [hS] at h2'
    have e : x * x * SC = (x * SC) * (x * SC) / SC := by field_simp
    have hlo : (a.lo:ℝ) < 0 := by exact_mod_cast (lt_of_not_ge ha)
    have hhi : (0:ℝ) < a.hi := by exact_mod_cast (lt_of_not_ge hb)
    constructor
    · simp only; push_cast; exact mul_nonneg (mul_self_nonneg x) SC_pos.le
    · simp only; rw [e]
      calc (x * SC) * (x * SC) / SC ≤ ((Max.max (a.lo * a.lo) (a.hi * a.hi) : ℤ) : ℝ) / SC := by
            gcongr
            push_cast
            rcases le_total 0 (x * SC) with h0 | h0
            · exact le_trans (by nlinarith) (le_max_right _ _)
            · exact le_trans (by nlinarith) (le_max_left _ _)
        _ ≤ _ := h2'

lemma mem_inv {y : ℝ} {b : Iv} (hy : ivMem y b) (hb : 0 < b.lo) : ivMem (1 / y) (inv b) := by
  obtain ⟨h3, h4⟩ := hy
  have hb' : (0:ℝ) < b.lo := by exact_mod_cast hb
  have hbhi : (0:ℤ) < b.hi := by
    have : (b.lo:ℝ) ≤ b.hi := le_trans h3 h4
    exact_mod_cast lt_of_lt_of_le hb' this
  have hY : 0 < y * SC := lt_of_lt_of_le hb' h3
  have hy0 : 0 < y := by
    rcases lt_or_ge 0 y with h | h
    · exact h
    · nlinarith [SC_pos]
  unfold inv; simp only [hb, ite_true]
  unfold ivMem; simp only
  have e : 1 / y * SC = SC * SC / (y * SC) := by field_simp
  rw [e]
  have h1 := divD_le (ONE * ONE) b.hi hbhi
  have h2 := le_divU (ONE * ONE) b.lo hb
  push_cast at h1 h2
  rw [ONE_cast] at h1 h2
  have hbh' : (0:ℝ) < b.hi := by exact_mod_cast hbhi
  constructor
  · calc ((divD (ONE * ONE) b.hi : ℤ) : ℝ) ≤ SC * SC / b.hi := h1
      _ ≤ SC * SC / (y * SC) := by gcongr
  · calc SC * SC / (y * SC) ≤ SC * SC / b.lo := by gcongr
      _ ≤ _ := h2

lemma mem_div {x y : ℝ} {a b : Iv} (hx : ivMem x a) (hy : ivMem y b) (hb : 0 < b.lo) :
    ivMem (x / y) (div a b) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  have hb' : (0:ℝ) < b.lo := by exact_mod_cast hb
  have hbhi : (0:ℤ) < b.hi := by
    have : (b.lo:ℝ) ≤ b.hi := le_trans h3 h4
    exact_mod_cast lt_of_lt_of_le hb' this
  have hbh' : (0:ℝ) < b.hi := by exact_mod_cast hbhi
  have hY : 0 < y * SC := lt_of_lt_of_le hb' h3
  have hy0 : 0 < y := by
    rcases lt_or_ge 0 y with h | h
    · exact h
    · nlinarith [SC_pos]
  unfold div; simp only [hb, ite_true]
  unfold ivMem; simp only
  have e : x / y * SC = (x * SC) * SC / (y * SC) := by field_simp
  rw [e]
  set X := x * SC
  set Y := y * SC
  constructor
  · split_ifs with ha
    · have h := divD_le (a.lo * ONE) b.hi hbhi
      push_cast at h; rw [ONE_cast] at h
      have ha' : (0:ℝ) ≤ a.lo := by exact_mod_cast ha
      calc _ ≤ (a.lo:ℝ) * SC / b.hi := h
        _ ≤ (a.lo:ℝ) * SC / Y := by gcongr
        _ ≤ X * SC / Y := by gcongr
    · have h := divD_le (a.lo * ONE) b.lo hb
      push_cast at h; rw [ONE_cast] at h
      have ha' : (a.lo:ℝ) < 0 := by exact_mod_cast (lt_of_not_ge ha)
      calc _ ≤ (a.lo:ℝ) * SC / b.lo := h
        _ ≤ (a.lo:ℝ) * SC / Y := by
          have hneg : (a.lo:ℝ) * SC < 0 := by nlinarith [SC_pos]
          rw [div_le_div_iff₀ hb' hY]; nlinarith [hneg, h3]
        _ ≤ X * SC / Y := by gcongr
  · split_ifs with ha
    · have h := le_divU (a.hi * ONE) b.lo hb
      push_cast at h; rw [ONE_cast] at h
      have ha' : (0:ℝ) ≤ a.hi := by exact_mod_cast ha
      calc X * SC / Y ≤ (a.hi:ℝ) * SC / Y := by gcongr
        _ ≤ (a.hi:ℝ) * SC / b.lo := by gcongr
        _ ≤ _ := h
    · have h := le_divU (a.hi * ONE) b.hi hbhi
      push_cast at h; rw [ONE_cast] at h
      have ha' : (a.hi:ℝ) < 0 := by exact_mod_cast (lt_of_not_ge ha)
      calc X * SC / Y ≤ (a.hi:ℝ) * SC / Y := by gcongr
        _ ≤ (a.hi:ℝ) * SC / b.hi := by
          have hneg : (a.hi:ℝ) * SC < 0 := by nlinarith [SC_pos]
          rw [div_le_div_iff₀ hY hbh']; nlinarith [hneg, h4]
        _ ≤ _ := h

lemma mem_min {x y : ℝ} {a b : Iv} (hx : ivMem x a) (hy : ivMem y b) : ivMem (Min.min x y) (min a b) := by
  unfold ivMem min at *; simp only; push_cast
  constructor
  · rcases le_total x y with h | h
    · rw [min_eq_left h]; exact le_trans (min_le_left _ _) hx.1
    · rw [min_eq_right h]; exact le_trans (min_le_right _ _) hy.1
  · rw [min_mul_of_nonneg _ _ SC_pos.le]
    exact min_le_min hx.2 hy.2

lemma mem_max {x y : ℝ} {a b : Iv} (hx : ivMem x a) (hy : ivMem y b) : ivMem (Max.max x y) (max a b) := by
  unfold ivMem max at *; simp only; push_cast
  constructor
  · rw [max_mul_of_nonneg _ _ SC_pos.le]
    exact max_le_max hx.1 hy.1
  · rcases le_total x y with h | h
    · rw [max_eq_right h]; exact le_trans hy.2 (le_max_right _ _)
    · rw [max_eq_left h]; exact le_trans hx.2 (le_max_left _ _)

lemma mem_abs {x : ℝ} {a : Iv} (hx : ivMem x a) : ivMem |x| (abs a) := by
  obtain ⟨h1, h2⟩ := hx
  unfold abs
  split_ifs with ha hb
  · have : (0:ℝ) ≤ a.lo := by exact_mod_cast ha
    have hx0 : 0 ≤ x := by nlinarith [SC_pos]
    rw [_root_.abs_of_nonneg hx0]; exact ⟨h1, h2⟩
  · have : (a.hi:ℝ) ≤ 0 := by exact_mod_cast hb
    have hx0 : x ≤ 0 := by nlinarith [SC_pos]
    rw [_root_.abs_of_nonpos hx0]; exact mem_neg ⟨h1, h2⟩
  · unfold ivMem; simp only; push_cast
    constructor
    · exact mul_nonneg (_root_.abs_nonneg x) SC_pos.le
    · rcases le_total 0 x with h0 | h0
      · rw [_root_.abs_of_nonneg h0]; exact le_trans h2 (le_max_right _ _)
      · rw [_root_.abs_of_nonpos h0]; exact le_trans (by linarith) (le_max_left _ _)

end Cert.Iv

/-! ## integer square roots -/

lemma isqrtLo_sq (n : ℕ) : isqrtLo n * isqrtLo n ≤ n := by
  unfold isqrtLo
  dsimp only
  split_ifs with h
  · exact h
  · simp

lemma le_isqrtHi_sq (n : ℕ) : n ≤ isqrtHi n * isqrtHi n := by
  unfold isqrtHi
  dsimp only
  split_ifs with h1 h2
  · exact h1
  · exact h2
  · nlinarith

namespace Cert.Iv

lemma mem_sqrt {x : ℝ} {a : Iv} (hx : ivMem x a) : ivMem (√x) (sqrt a) := by
  obtain ⟨h1, h2⟩ := hx
  unfold sqrt ivMem
  simp only
  have hS := SC_pos
  have key : √x * SC = √(x * SC * SC) := by
    rw [mul_assoc, Real.sqrt_mul' x (by positivity : (0:ℝ) ≤ SC * SC), Real.sqrt_mul_self hS.le]
  rw [key]
  constructor
  · split_ifs with ha
    · simp
    · have ha' : 0 < a.lo := lt_of_not_ge ha
      have hn : ((a.lo * ONE).toNat : ℝ) = (a.lo : ℝ) * SC := by
        have : 0 ≤ a.lo * ONE := by unfold ONE; positivity
        rw [show ((a.lo * ONE).toNat : ℝ) = (((a.lo * ONE).toNat : ℤ) : ℝ) by norm_cast]
        rw [Int.toNat_of_nonneg this]; push_cast; rw [ONE_cast]
      have hsq := isqrtLo_sq (a.lo * ONE).toNat
      have hsq' : ((isqrtLo (a.lo * ONE).toNat : ℝ)) ^ 2 ≤ x * SC * SC := by
        have : ((isqrtLo (a.lo * ONE).toNat : ℝ)) ^ 2 ≤ ((a.lo * ONE).toNat : ℝ) := by
          rw [sq]; exact_mod_cast hsq
        rw [hn] at this
        nlinarith
      push_cast
      exact Real.le_sqrt_of_sq_le hsq'
  · split_ifs with ha
    · have : x * SC ≤ 0 := le_trans h2 (by exact_mod_cast ha)
      have : x * SC * SC ≤ 0 := by nlinarith
      rw [Real.sqrt_eq_zero'.mpr this]; simp
    · have ha' : 0 < a.hi := lt_of_not_ge ha
      have hn : ((a.hi * ONE).toNat : ℝ) = (a.hi : ℝ) * SC := by
        have : 0 ≤ a.hi * ONE := by unfold ONE; positivity
        rw [show ((a.hi * ONE).toNat : ℝ) = (((a.hi * ONE).toNat : ℤ) : ℝ) by norm_cast]
        rw [Int.toNat_of_nonneg this]; push_cast; rw [ONE_cast]
      have hsq := le_isqrtHi_sq (a.hi * ONE).toNat
      have hsq' : x * SC * SC ≤ ((isqrtHi (a.hi * ONE).toNat : ℝ)) ^ 2 := by
        have : ((a.hi * ONE).toNat : ℝ) ≤ ((isqrtHi (a.hi * ONE).toNat : ℝ)) ^ 2 := by
          rw [sq]; exact_mod_cast hsq
        rw [hn] at this
        nlinarith
      push_cast
      exact Real.sqrt_le_iff.mpr ⟨by positivity, hsq'⟩

end Cert.Iv

end BHH
