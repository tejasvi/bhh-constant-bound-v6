/-
Soundness of `cosSin` (module A): Taylor polynomials with the remainder of `Complex.exp_bound`, then doubling.
-/
import BHH.Ivl.Basic

open BHH.Cert Complex Finset

namespace BHH

/-! ## Taylor polynomials of cos and sin -/

/-- the terms of the cosine series with index `< n` -/
noncomputable def cosPart (n : ℕ) (s : ℝ) : ℝ :=
  ∑ m ∈ range n, (if m % 4 = 0 then s ^ m / m.factorial else if m % 4 = 2 then -(s ^ m / m.factorial) else 0)

/-- the terms of the sine series with index `< n` -/
noncomputable def sinPart (n : ℕ) (s : ℝ) : ℝ :=
  ∑ m ∈ range n, (if m % 4 = 1 then s ^ m / m.factorial else if m % 4 = 3 then -(s ^ m / m.factorial) else 0)

lemma I_pow_mod (m : ℕ) : (I : ℂ) ^ m = I ^ (m % 4) := by
  conv_lhs => rw [← Nat.div_add_mod m 4, pow_add, pow_mul]
  simp [I_pow_four]

lemma cosPart_succ (m : ℕ) (s : ℝ) :
    cosPart (m + 1) s = cosPart m s +
      (if m % 4 = 0 then s ^ m / m.factorial else if m % 4 = 2 then -(s ^ m / m.factorial) else 0) := by
  simp [cosPart, sum_range_succ]

lemma sinPart_succ (m : ℕ) (s : ℝ) :
    sinPart (m + 1) s = sinPart m s +
      (if m % 4 = 1 then s ^ m / m.factorial else if m % 4 = 3 then -(s ^ m / m.factorial) else 0) := by
  simp [sinPart, sum_range_succ]

lemma partial_eq (n : ℕ) (s : ℝ) :
    (∑ m ∈ range n, ((s : ℂ) * I) ^ m / (m.factorial : ℂ)) = (cosPart n s : ℂ) + (sinPart n s : ℂ) * I := by
  induction n with
  | zero => simp [cosPart, sinPart]
  | succ n ih =>
    rw [sum_range_succ, ih, cosPart_succ, sinPart_succ, mul_pow, I_pow_mod]
    have h4 : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases h : n % 4 <;> simp [h, I_sq, pow_succ] <;> push_cast <;> ring

lemma cos_sin_taylor (s : ℝ) (hs : |s| ≤ 1) (n : ℕ) (hn : 0 < n) :
    |Real.cos s - cosPart n s| ≤ |s| ^ n * ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹) ∧
    |Real.sin s - sinPart n s| ≤ |s| ^ n * ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹) := by
  have hx : ‖(s : ℂ) * I‖ ≤ 1 := by simpa [Complex.norm_real] using hs
  have hb := Complex.exp_bound hx hn
  rw [partial_eq, Complex.exp_mul_I] at hb
  have hnorm : ‖(s : ℂ) * I‖ = |s| := by simp [Complex.norm_mul, Complex.norm_real]
  rw [hnorm] at hb
  have e : Complex.cos ↑s + Complex.sin ↑s * I - (↑(cosPart n s) + ↑(sinPart n s) * I)
      = ((Real.cos s - cosPart n s : ℝ) : ℂ) + ((Real.sin s - sinPart n s : ℝ) : ℂ) * I := by
    push_cast; rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]; ring
  rw [e] at hb
  constructor
  · calc |Real.cos s - cosPart n s|
        = |(((Real.cos s - cosPart n s : ℝ) : ℂ) + ((Real.sin s - sinPart n s : ℝ) : ℂ) * I).re| := by
          simp [Complex.cos_ofReal_re]
      _ ≤ ‖((Real.cos s - cosPart n s : ℝ) : ℂ) + ((Real.sin s - sinPart n s : ℝ) : ℂ) * I‖ :=
          Complex.abs_re_le_norm _
      _ ≤ _ := hb
  · calc |Real.sin s - sinPart n s|
        = |(((Real.cos s - cosPart n s : ℝ) : ℂ) + ((Real.sin s - sinPart n s : ℝ) : ℂ) * I).im| := by
          simp [Complex.sin_ofReal_re]
      _ ≤ ‖((Real.cos s - cosPart n s : ℝ) : ℂ) + ((Real.sin s - sinPart n s : ℝ) : ℂ) * I‖ :=
          Complex.abs_im_le_norm _
      _ ≤ _ := hb

/-! ## the Taylor recursion -/

/-- one step of the term recursion: `term ∋ τ` gives `nt ∋ τ s / (m+1)`, `s = t / 2^(PR + r)` -/
lemma mem_term_step {τ : ℝ} {term : Iv} (h : ivMem τ term) (t : ℤ) (r m : ℕ) :
    ivMem (τ * ((t : ℝ) / 2 ^ (PR + r)) / (m + 1 : ℕ))
      ⟨divD (shrD (if 0 ≤ t then term.lo * t else term.hi * t) (PR + r)) (m + 1),
       divU (shrU (if 0 ≤ t then term.hi * t else term.lo * t) (PR + r)) (m + 1)⟩ := by
  obtain ⟨h1, h2⟩ := h
  have hm : (0:ℤ) < (m + 1 : ℕ) := by positivity
  have hm' : (0:ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hP : (0:ℝ) < 2 ^ (PR + r) := by positivity
  -- the exact value scaled: (τ s / (m+1)) SC = ((τ SC) t / 2^(PR+r)) / (m+1)
  have e : τ * ((t : ℝ) / 2 ^ (PR + r)) / ((m + 1 : ℕ) : ℝ) * SC
      = (τ * SC) * t / 2 ^ (PR + r) / ((m + 1 : ℕ) : ℝ) := by ring
  -- bounds on (τ SC) t
  have hlo : ((if 0 ≤ t then term.lo * t else term.hi * t : ℤ) : ℝ) ≤ (τ * SC) * t := by
    split_ifs with ht
    · have : (0:ℝ) ≤ t := by exact_mod_cast ht
      push_cast; nlinarith
    · have : (t:ℝ) < 0 := by exact_mod_cast lt_of_not_ge ht
      push_cast; nlinarith
  have hhi : (τ * SC) * t ≤ ((if 0 ≤ t then term.hi * t else term.lo * t : ℤ) : ℝ) := by
    split_ifs with ht
    · have : (0:ℝ) ≤ t := by exact_mod_cast ht
      push_cast; nlinarith
    · have : (t:ℝ) < 0 := by exact_mod_cast lt_of_not_ge ht
      push_cast; nlinarith
  unfold ivMem; simp only; rw [e]
  constructor
  · have a1 := shrD_le (if 0 ≤ t then term.lo * t else term.hi * t) (PR + r)
    have a2 := divD_le (shrD (if 0 ≤ t then term.lo * t else term.hi * t) (PR + r)) (m + 1 : ℕ) hm
    push_cast at a2 ⊢
    calc _ ≤ ((shrD (if 0 ≤ t then term.lo * t else term.hi * t) (PR + r) : ℤ) : ℝ) / ((m:ℝ) + 1) := a2
      _ ≤ (((if 0 ≤ t then term.lo * t else term.hi * t : ℤ) : ℝ) / 2 ^ (PR + r)) / ((m:ℝ) + 1) := by
          gcongr
      _ ≤ (τ * SC) * t / 2 ^ (PR + r) / ((m:ℝ) + 1) := by gcongr
  · have a1 := le_shrU (if 0 ≤ t then term.hi * t else term.lo * t) (PR + r)
    have a2 := le_divU (shrU (if 0 ≤ t then term.hi * t else term.lo * t) (PR + r)) (m + 1 : ℕ) hm
    push_cast at a2 ⊢
    calc (τ * SC) * t / 2 ^ (PR + r) / ((m:ℝ) + 1)
        ≤ (((if 0 ≤ t then term.hi * t else term.lo * t : ℤ) : ℝ) / 2 ^ (PR + r)) / ((m:ℝ) + 1) := by
          gcongr
      _ ≤ ((shrU (if 0 ≤ t then term.hi * t else term.lo * t) (PR + r) : ℤ) : ℝ) / ((m:ℝ) + 1) := by
          gcongr
      _ ≤ _ := a2

lemma taylorGo_spec (t : ℤ) (r n : ℕ) :
    ∀ fuel m term c sa, m ≤ n → n < m + fuel →
      ivMem (((t : ℝ) / 2 ^ (PR + r)) ^ m / m.factorial) term →
      ivMem (cosPart m ((t : ℝ) / 2 ^ (PR + r))) c →
      ivMem (sinPart m ((t : ℝ) / 2 ^ (PR + r))) sa →
      ivMem (cosPart n ((t : ℝ) / 2 ^ (PR + r))) (taylorGo t r n fuel m term c sa).1 ∧
      ivMem (sinPart n ((t : ℝ) / 2 ^ (PR + r))) (taylorGo t r n fuel m term c sa).2.1 ∧
      ivMem (((t : ℝ) / 2 ^ (PR + r)) ^ n / n.factorial) (taylorGo t r n fuel m term c sa).2.2 := by
  intro fuel
  induction fuel with
  | zero => intro m _ _ _ hmn hlt; omega
  | succ fuel ih =>
    intro m term c sa hmn hlt hterm hc hs
    set s := (t : ℝ) / 2 ^ (PR + r)
    unfold taylorGo
    by_cases hm : m = n
    · subst hm; simp only [beq_self_eq_true, ite_true]; exact ⟨hc, hs, hterm⟩
    · have hm' : (m == n) = false := by simpa using hm
      simp only [hm', Bool.false_eq_true, ite_false]
      apply ih (m + 1) _ _ _ (by omega) (by omega)
      · -- next term
        have := mem_term_step hterm t r m
        rw [show s ^ (m + 1) / ((m + 1).factorial : ℝ) = s ^ m / m.factorial * s / ((m + 1 : ℕ) : ℝ) by
          rw [Nat.factorial_succ]; push_cast; field_simp; ring]
        exact this
      · rw [cosPart_succ]
        have h4 : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
        interval_cases h : m % 4
        · simpa [h] using Iv.mem_add hc hterm
        · simpa [h] using hc
        · simpa [h, sub_eq_add_neg] using Iv.mem_sub hc hterm
        · simpa [h] using hc
      · rw [sinPart_succ]
        have h4 : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
        interval_cases h : m % 4
        · simpa [h] using hs
        · simpa [h] using Iv.mem_add hs hterm
        · simpa [h] using hs
        · simpa [h, sub_eq_add_neg] using Iv.mem_sub hs hterm

/-! ## sinCosSmall, doubling, cosSin -/

lemma mag_bound {x : ℝ} {a : Iv} (h : ivMem x a) :
    |x| * SC ≤ ((Max.max (Int.natAbs a.lo) (Int.natAbs a.hi) : ℕ) : ℝ) := by
  obtain ⟨h1, h2⟩ := h
  have hS := SC_pos
  have e : |x| * SC = |x * SC| := by rw [abs_mul, abs_of_pos hS]
  rw [e]
  push_cast
  rcases le_total 0 (x * SC) with h0 | h0
  · rw [abs_of_nonneg h0]
    have : (a.hi : ℝ) ≤ |(a.hi : ℝ)| := le_abs_self _
    have h3 : (|(a.hi : ℝ)|) = ((Int.natAbs a.hi : ℕ) : ℝ) := by
      rw [Nat.cast_natAbs]; push_cast; rfl
    calc x * SC ≤ a.hi := h2
      _ ≤ ((Int.natAbs a.hi : ℕ) : ℝ) := by rw [← h3]; exact this
      _ ≤ _ := by exact_mod_cast le_max_right _ _
  · rw [abs_of_nonpos h0]
    have h3 : (|(a.lo : ℝ)|) = ((Int.natAbs a.lo : ℕ) : ℝ) := by
      rw [Nat.cast_natAbs]; push_cast; rfl
    calc -(x * SC) ≤ -(a.lo : ℝ) := by linarith
      _ ≤ |(a.lo : ℝ)| := neg_le_abs _
      _ = ((Int.natAbs a.lo : ℕ) : ℝ) := h3
      _ ≤ _ := by exact_mod_cast le_max_left _ _

/-- widening an enclosure of an approximation `p` of `x` by a bound of `|x - p|` -/
lemma mem_widen_of_approx {x p E : ℝ} {lo hi rem : ℤ} (h1 : (lo : ℝ) ≤ p * SC) (h2 : p * SC ≤ hi)
    (h3 : |x - p| ≤ E) (h4 : E * SC ≤ (rem : ℝ)) : ivMem x (Iv.widen ⟨lo, hi⟩ rem) := by
  have hS := SC_pos
  unfold ivMem Iv.widen; simp only; push_cast
  have h := abs_sub_le_iff.mp h3
  have a1 := mul_le_mul_of_nonneg_right h.1 hS.le
  have a2 := mul_le_mul_of_nonneg_right h.2 hS.le
  constructor <;> nlinarith

lemma sinCosSmall_spec (t : ℤ) (r : ℕ) (ht : |(t : ℝ) / 2 ^ (PR + r)| ≤ 1) :
    ivMem (Real.cos ((t : ℝ) / 2 ^ (PR + r))) (sinCosSmall t r).1 ∧
    ivMem (Real.sin ((t : ℝ) / 2 ^ (PR + r))) (sinCosSmall t r).2 := by
  have h0 : ivMem (((t : ℝ) / 2 ^ (PR + r)) ^ 0 / (Nat.factorial 0 : ℝ)) (Iv.int 1) := by
    simpa using Iv.mem_int 1
  have hc0 : ivMem (cosPart 0 ((t : ℝ) / 2 ^ (PR + r))) ⟨0, 0⟩ := by simp [cosPart, ivMem]
  have hs0 : ivMem (sinPart 0 ((t : ℝ) / 2 ^ (PR + r))) ⟨0, 0⟩ := by simp [sinPart, ivMem]
  obtain ⟨hc, hsn, hlast⟩ :=
    taylorGo_spec t r NTERMS (NTERMS + 1) 0 (Iv.int 1) ⟨0, 0⟩ ⟨0, 0⟩ (by norm_num) (by norm_num) h0 hc0 hs0
  have hb := cos_sin_taylor ((t : ℝ) / 2 ^ (PR + r)) ht NTERMS (by norm_num [NTERMS])
  generalize hres : taylorGo t r NTERMS (NTERMS + 1) 0 (Iv.int 1) ⟨0, 0⟩ ⟨0, 0⟩ = res at hc hsn hlast
  obtain ⟨c, sa, last⟩ := res
  simp only at hc hsn hlast
  generalize hsdef : (t : ℝ) / 2 ^ (PR + r) = s at hc hsn hlast hb ht ⊢
  have hS := SC_pos
  have hmag := mag_bound hlast
  have hfac : (0:ℝ) < (NTERMS.factorial : ℝ) := by positivity
  have hpow : |s ^ NTERMS / (NTERMS.factorial : ℝ)| = |s| ^ NTERMS / NTERMS.factorial := by
    rw [abs_div, abs_pow, abs_of_pos hfac]
  rw [hpow] at hmag
  generalize hmagdef : Max.max (Int.natAbs last.lo) (Int.natAbs last.hi) = mag at hmag
  have hN : (0:ℝ) < NTERMS := by norm_num [NTERMS]
  have hrem : |s| ^ NTERMS * ((NTERMS.succ : ℝ) * (NTERMS.factorial * NTERMS : ℝ)⁻¹) * SC
      ≤ ((divU ((mag : ℤ) * (NTERMS + 1)) NTERMS + 1 : ℤ) : ℝ) := by
    have h2 := le_divU ((mag : ℤ) * (NTERMS + 1)) NTERMS (by norm_num [NTERMS])
    have e : |s| ^ NTERMS * ((NTERMS.succ : ℝ) * (NTERMS.factorial * NTERMS : ℝ)⁻¹) * SC
        = (|s| ^ NTERMS / NTERMS.factorial * SC) * ((NTERMS : ℝ) + 1) / NTERMS := by
      push_cast; field_simp
    rw [e]
    push_cast at h2 ⊢
    calc (|s| ^ NTERMS / NTERMS.factorial * SC) * ((NTERMS : ℝ) + 1) / NTERMS
        ≤ (mag : ℝ) * ((NTERMS : ℝ) + 1) / NTERMS := by gcongr
      _ ≤ _ := h2
      _ ≤ _ := by linarith
  have heq : sinCosSmall t r = (Iv.widen c (divU ((mag : ℤ) * (NTERMS + 1)) NTERMS + 1),
      Iv.widen sa (divU ((mag : ℤ) * (NTERMS + 1)) NTERMS + 1)) := by
    unfold sinCosSmall
    rw [hres, ← hmagdef]
  rw [heq]
  exact ⟨mem_widen_of_approx hc.1 hc.2 hb.1 hrem, mem_widen_of_approx hsn.1 hsn.2 hb.2 hrem⟩

lemma dbl_spec {x : ℝ} {c s : Iv} (hc : ivMem (Real.cos x) c) (hs : ivMem (Real.sin x) s) :
    ivMem (Real.cos (2 * x)) (dbl (c, s)).1 ∧ ivMem (Real.sin (2 * x)) (dbl (c, s)).2 := by
  unfold dbl; simp only
  constructor
  · rw [Real.cos_two_mul_eq_one_sub]
    have h := Iv.mem_sub (Iv.mem_int 1) (Iv.mem_mul2e (Iv.mem_sqr hs) 1)
    simpa [mul_comm] using h
  · rw [Real.sin_two_mul]
    have h := Iv.mem_mul2e (Iv.mem_mul hs hc) 1
    simpa [mul_comm, mul_assoc, mul_left_comm] using h

lemma dblN_spec : ∀ (n : ℕ) {x : ℝ} {c s : Iv}, ivMem (Real.cos x) c → ivMem (Real.sin x) s →
    ivMem (Real.cos (2 ^ n * x)) (dblN n (c, s)).1 ∧ ivMem (Real.sin (2 ^ n * x)) (dblN n (c, s)).2
  | 0, x, c, s, hc, hs => by simpa [dblN] using ⟨hc, hs⟩
  | n + 1, x, c, s, hc, hs => by
    have h := dbl_spec hc hs
    unfold dblN
    have := dblN_spec n h.1 h.2
    rw [show (2:ℝ) ^ (n + 1) * x = 2 ^ n * (2 * x) by ring]
    exact this

lemma clip1_cos {x : ℝ} {a : Iv} (h : ivMem (Real.cos x) a) : ivMem (Real.cos x) (clip1 a) := by
  obtain ⟨h1, h2⟩ := h
  unfold clip1 ivMem; simp only; push_cast; rw [ONE_cast]
  have := Real.neg_one_le_cos x
  have := Real.cos_le_one x
  have hS := SC_pos
  constructor
  · exact max_le h1 (by nlinarith)
  · exact le_min h2 (by nlinarith)

lemma clip1_sin {x : ℝ} {a : Iv} (h : ivMem (Real.sin x) a) : ivMem (Real.sin x) (clip1 a) := by
  obtain ⟨h1, h2⟩ := h
  unfold clip1 ivMem; simp only; push_cast; rw [ONE_cast]
  have := Real.neg_one_le_sin x
  have := Real.sin_le_one x
  have hS := SC_pos
  constructor
  · exact max_le h1 (by nlinarith)
  · exact le_min h2 (by nlinarith)

theorem cosSin_sound : CosSinSound cosSin := by
  intro t ht
  have hONE : ONE.toNat = 2 ^ PR := by simp [ONE, PR]
  have ht8 : t.natAbs ≤ 8 * ONE.toNat := by omega
  unfold cosSin
  simp only [ht8, ite_true]
  -- |t / 2^(PR+4)| ≤ 1/2
  have habs : |(t : ℝ) / 2 ^ (PR + 4)| ≤ 1 := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 ^ (PR + 4))]
    rw [div_le_one (by positivity)]
    have h8 : ((t.natAbs : ℕ) : ℝ) ≤ 8 * 2 ^ PR := by
      rw [hONE] at ht8; exact_mod_cast ht8
    rw [Nat.cast_natAbs] at h8
    calc |(t:ℝ)| ≤ 8 * 2 ^ PR := by simpa using h8
      _ ≤ 2 ^ (PR + 4) := by
          rw [pow_add]; have : (0:ℝ) < 2 ^ PR := by positivity
          nlinarith
  have h1 := sinCosSmall_spec t 4 habs
  have h2 := dblN_spec 4 h1.1 h1.2
  have e : (2:ℝ) ^ 4 * ((t : ℝ) / 2 ^ (PR + 4)) = fx t := by
    unfold fx; rw [pow_add]; field_simp
  rw [e] at h2
  exact ⟨clip1_cos h2.1, clip1_sin h2.2⟩

end BHH
