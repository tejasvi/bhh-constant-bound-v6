/-
Soundness of `phiAt` (module A): enclosures of `φ(x) = x^{-s}`, `φ'(x) = -s x^{-s-1}`, `φ''(x) = s(s+1) x^{-s-2}`,
`s = k - 1/2`, at the exact point `x = t / 2^PR`.
-/
import BHH.Ivl.Trig

open BHH.Cert

namespace BHH

lemma mem_pow_fold (x : ℝ) (t : ℤ) (hx : ivMem x (Iv.pt t)) :
    ∀ j : ℕ, ∀ (acc : Iv) (n : ℕ), ivMem (x ^ n) acc →
      ivMem (x ^ (n + j)) ((List.range j).foldl (fun a _ => Iv.mul a (Iv.pt t)) acc) := by
  intro j
  induction j with
  | zero => intro acc n h; simpa using h
  | succ j ih =>
    intro acc n h
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    have := Iv.mem_mul (ih acc n h) hx
    rw [show n + (j + 1) = n + j + 1 by omega, pow_succ]
    exact this

/-- `x^{-(k - 1/2)} = √x / x^k` for `x > 0` -/
lemma rpow_half_eq {x : ℝ} (hx : 0 < x) (k : ℕ) :
    x ^ (-((k : ℝ) - 1 / 2)) = √x / x ^ k := by
  rw [Real.sqrt_eq_rpow, show -((k : ℝ) - 1 / 2) = 1 / 2 - (k : ℝ) by ring, Real.rpow_sub hx,
    Real.rpow_natCast]

theorem phiAt_sound (k : ℕ) (hk : 1 ≤ k) (t : ℤ) (f0 f1 f2 : Iv) (h : phiAt k t = some (f0, f1, f2)) :
    0 < fx t ∧
    ivMem ((fx t) ^ (-((k : ℝ) - 1 / 2))) f0 ∧
    ivMem (-((k : ℝ) - 1 / 2) * (fx t) ^ (-((k : ℝ) - 1 / 2) - 1)) f1 ∧
    ivMem (((k : ℝ) - 1 / 2) * ((k : ℝ) - 1 / 2 + 1) * (fx t) ^ (-((k : ℝ) - 1 / 2) - 2)) f2 := by
  unfold phiAt at h
  dsimp only at h
  split_ifs at h with h1 h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hf0, hf1, hf2⟩ := h
  have htpos : (0:ℤ) < t := lt_of_lt_of_le (by positivity) (not_lt.mp h1)
  have hx : 0 < fx t := by unfold fx; positivity
  have hpt := Iv.mem_pt t
  have htk := mem_pow_fold (fx t) t hpt k (Iv.int 1) 0 (by simpa using Iv.mem_int 1)
  simp only [zero_add] at htk
  have hptlo : 0 < (Iv.pt t).lo := by simp [Iv.pt]; exact htpos
  have hdiv0 := Iv.mem_div (Iv.mem_sqrt hpt) htk (lt_of_not_ge h2)
  set x := fx t
  set s : ℝ := (k : ℝ) - 1 / 2
  have hphi : x ^ (-s) = √x / x ^ k := rpow_half_eq hx k
  refine ⟨hx, ?_, ?_, ?_⟩
  · rw [← hf0, hphi]; exact hdiv0
  · -- φ' = -(φ/x · (2k-1))/2
    have e : -s * x ^ (-s - 1) = -((√x / x ^ k) / x * ((2 * k - 1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) := by
      rw [Real.rpow_sub_one (ne_of_gt hx), hphi]
      push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * k)]; simp only [s]; ring
    rw [e, ← hf1]
    exact Iv.mem_neg (Iv.mem_divNat (Iv.mem_mulNat (Iv.mem_div hdiv0 hpt hptlo) _) (by norm_num))
  · have e : s * (s + 1) * x ^ (-s - 2) =
        (√x / x ^ k) / x / x * (((2 * k - 1) * (2 * k - 1 + 2) : ℕ) : ℝ) / ((4 : ℕ) : ℝ) := by
      rw [show -s - 2 = (-s - 1) - 1 by ring, Real.rpow_sub_one (ne_of_gt hx),
        Real.rpow_sub_one (ne_of_gt hx), hphi]
      push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * k)]; simp only [s]; ring
    rw [e, ← hf2]
    exact Iv.mem_divNat (Iv.mem_mulNat (Iv.mem_div (Iv.mem_div hdiv0 hpt hptlo) hpt hptlo) _) (by norm_num)

end BHH
