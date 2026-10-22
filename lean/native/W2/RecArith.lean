/-
Arithmetic facts behind the production recursion `W2C.runT4`: the scalar product bounds `mulTop`, the 31-bit
halves, the directed rounding `rnd`.
-/
import Mathlib
import W2Cert.Rec

namespace BHH.W2

open W2C

lemma m31_eq : m31 = 2 ^ 31 - 1 := rfl

lemma and_m31_lt (G : ℕ) : G &&& m31 < 2 ^ 31 := by
  rw [m31_eq, Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (by norm_num)

lemma split31 (G : ℕ) : G = (G >>> 31) * 2 ^ 31 + (G &&& m31) := by
  rw [m31_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  exact (Nat.div_add_mod' G (2 ^ 31)).symm

lemma mulTop_lower_nat (g1 g0 k1 k0 : ℕ) :
    mulTop true g1 g0 k1 k0 * 2 ^ 76 ≤ (g1 * 2 ^ 31 + g0) * (k1 * 2 ^ 31 + k0) := by
  unfold mulTop
  simp only [ite_true]
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have h1 : g1 * k1 / 2 ^ 14 * 2 ^ 14 ≤ g1 * k1 := Nat.div_mul_le_self _ _
  have h2 : (g1 * k0 + g0 * k1) / 2 ^ 45 * 2 ^ 45 ≤ g1 * k0 + g0 * k1 := Nat.div_mul_le_self _ _
  have e : (g1 * 2 ^ 31 + g0) * (k1 * 2 ^ 31 + k0) =
      g1 * k1 * 2 ^ 62 + (g1 * k0 + g0 * k1) * 2 ^ 31 + g0 * k0 := by ring
  rw [e, add_mul]
  have a1 : g1 * k1 / 2 ^ 14 * 2 ^ 76 ≤ g1 * k1 * 2 ^ 62 := by
    calc g1 * k1 / 2 ^ 14 * 2 ^ 76 = (g1 * k1 / 2 ^ 14 * 2 ^ 14) * 2 ^ 62 := by ring
      _ ≤ g1 * k1 * 2 ^ 62 := Nat.mul_le_mul_right _ h1
  have a2 : (g1 * k0 + g0 * k1) / 2 ^ 45 * 2 ^ 76 ≤ (g1 * k0 + g0 * k1) * 2 ^ 31 := by
    calc (g1 * k0 + g0 * k1) / 2 ^ 45 * 2 ^ 76 = ((g1 * k0 + g0 * k1) / 2 ^ 45 * 2 ^ 45) * 2 ^ 31 := by ring
      _ ≤ (g1 * k0 + g0 * k1) * 2 ^ 31 := Nat.mul_le_mul_right _ h2
  have h0 : 0 ≤ g0 * k0 := Nat.zero_le _
  linarith

/-- `mulTop true` is a lower bound of `G K / 2^76`. -/
lemma mulTop_lower_le (g1 g0 k1 k0 : ℕ) :
    (mulTop true g1 g0 k1 k0 : ℝ) ≤ ((g1 * 2 ^ 31 + g0) * (k1 * 2 ^ 31 + k0) : ℕ) / (2 : ℝ) ^ 76 := by
  rw [le_div_iff₀ (by positivity)]
  have := mulTop_lower_nat g1 g0 k1 k0
  exact_mod_cast this

lemma mulTop_upper_nat (g1 g0 k1 k0 : ℕ) (hg : g0 < 2 ^ 31) (hk : k0 < 2 ^ 31) :
    (g1 * 2 ^ 31 + g0) * (k1 * 2 ^ 31 + k0) ≤ mulTop false g1 g0 k1 k0 * 2 ^ 76 := by
  unfold mulTop
  simp only [Bool.false_eq_true, ite_false]
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  set q1 := g1 * k1 / 2 ^ 14
  set q2 := (g1 * k0 + g0 * k1) / 2 ^ 45
  have h1 : g1 * k1 < q1 * 2 ^ 14 + 2 ^ 14 := Nat.lt_div_mul_add (by positivity)
  have h2 : g1 * k0 + g0 * k1 < q2 * 2 ^ 45 + 2 ^ 45 := Nat.lt_div_mul_add (by positivity)
  have h3 : g0 * k0 < 2 ^ 62 := by
    calc g0 * k0 < 2 ^ 31 * 2 ^ 31 := Nat.mul_lt_mul'' hg hk
      _ = 2 ^ 62 := by norm_num
  have e : (g1 * 2 ^ 31 + g0) * (k1 * 2 ^ 31 + k0) =
      g1 * k1 * 2 ^ 62 + (g1 * k0 + g0 * k1) * 2 ^ 31 + g0 * k0 := by ring
  rw [e]
  have a1 : g1 * k1 * 2 ^ 62 ≤ (q1 + 1) * 2 ^ 76 := by
    have : g1 * k1 ≤ (q1 + 1) * 2 ^ 14 := by rw [add_mul, one_mul]; exact h1.le
    calc g1 * k1 * 2 ^ 62 ≤ (q1 + 1) * 2 ^ 14 * 2 ^ 62 := Nat.mul_le_mul_right _ this
      _ = (q1 + 1) * 2 ^ 76 := by ring
  have a2 : (g1 * k0 + g0 * k1) * 2 ^ 31 ≤ (q2 + 1) * 2 ^ 76 := by
    have : g1 * k0 + g0 * k1 ≤ (q2 + 1) * 2 ^ 45 := by rw [add_mul, one_mul]; exact h2.le
    calc (g1 * k0 + g0 * k1) * 2 ^ 31 ≤ (q2 + 1) * 2 ^ 45 * 2 ^ 31 := Nat.mul_le_mul_right _ this
      _ = (q2 + 1) * 2 ^ 76 := by ring
  have a3 : g0 * k0 ≤ 1 * 2 ^ 76 := by
    have : (2:ℕ) ^ 62 ≤ 1 * 2 ^ 76 := by norm_num
    linarith
  calc g1 * k1 * 2 ^ 62 + (g1 * k0 + g0 * k1) * 2 ^ 31 + g0 * k0
      ≤ (q1 + 1) * 2 ^ 76 + (q2 + 1) * 2 ^ 76 + 1 * 2 ^ 76 := by linarith
    _ = (q1 + q2 + 3) * 2 ^ 76 := by ring

/-- `mulTop false` is an upper bound of `G K / 2^76` (31-bit low halves). -/
lemma le_mulTop_upper (g1 g0 k1 k0 : ℕ) (hg : g0 < 2 ^ 31) (hk : k0 < 2 ^ 31) :
    ((g1 * 2 ^ 31 + g0) * (k1 * 2 ^ 31 + k0) : ℕ) / (2 : ℝ) ^ 76 ≤ (mulTop false g1 g0 k1 k0 : ℝ) := by
  rw [div_le_iff₀ (by positivity)]
  have := mulTop_upper_nat g1 g0 k1 k0 hg hk
  exact_mod_cast this

/-- Directed rounding of `v / 2^sh`. -/
lemma rnd_lower_le (v sh : ℕ) : (rnd true v sh : ℝ) ≤ (v : ℝ) / 2 ^ sh := by
  unfold rnd; simp only [ite_true]; rw [Nat.shiftRight_eq_div_pow, le_div_iff₀ (by positivity)]
  have := Nat.div_mul_le_self v (2 ^ sh)
  exact_mod_cast this

lemma nat_le_ceil_mul (v N : ℕ) (hN : 1 ≤ N) : v ≤ (v + (N - 1)) / N * N := by
  have hdm := Nat.div_add_mod (v + (N - 1)) N
  have hm := Nat.mod_lt (v + (N - 1)) (show 0 < N by omega)
  generalize (v + (N - 1)) / N = q at hdm ⊢
  generalize (v + (N - 1)) % N = r at hdm hm
  rw [mul_comm] at hdm
  omega

lemma le_rnd_upper (v sh : ℕ) : (v : ℝ) / 2 ^ sh ≤ (rnd false v sh : ℝ) := by
  unfold rnd; simp only [Bool.false_eq_true, ite_false]; rw [Nat.shiftRight_eq_div_pow, div_le_iff₀ (by positivity)]
  have := nat_le_ceil_mul v (2 ^ sh) Nat.one_le_two_pow
  exact_mod_cast this

end BHH.W2
