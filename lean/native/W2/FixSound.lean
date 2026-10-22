/-
Soundness of the extra fixed-point functions of `W2Cert/Fix.lean`: `exp` (Taylor + `Real.exp_bound` + squaring),
`log`, `arccos`, `arcsin` (by verification) and the closed form of `A_1`.
-/
import BHH.Ivl.Asin
import W2Cert.Fix

open BHH.Cert Finset Real

namespace BHH.W2

open BHH

/-- partial sums of the exponential series -/
noncomputable def expPart (n : ℕ) (s : ℝ) : ℝ := ∑ m ∈ range n, s ^ m / m.factorial

lemma expPart_succ (m : ℕ) (s : ℝ) : expPart (m + 1) s = expPart m s + s ^ m / m.factorial := by
  simp [expPart, sum_range_succ]

lemma expTaylorGo_spec (t : ℤ) (r n : ℕ) :
    ∀ fuel m term sa, m ≤ n → n < m + fuel →
      ivMem (((t : ℝ) / 2 ^ (PR + r)) ^ m / m.factorial) term →
      ivMem (expPart m ((t : ℝ) / 2 ^ (PR + r))) sa →
      ivMem (expPart n ((t : ℝ) / 2 ^ (PR + r))) (W2C.expTaylorGo t r n fuel m term sa).1 ∧
      ivMem (((t : ℝ) / 2 ^ (PR + r)) ^ n / n.factorial) (W2C.expTaylorGo t r n fuel m term sa).2 := by
  intro fuel
  induction fuel with
  | zero => intro m _ _ hmn hlt; omega
  | succ fuel ih =>
    intro m term sa hmn hlt hterm hs
    set s := (t : ℝ) / 2 ^ (PR + r)
    unfold W2C.expTaylorGo
    by_cases hm : m = n
    · subst hm; simp only [beq_self_eq_true, ite_true]; exact ⟨hs, hterm⟩
    · have hm' : (m == n) = false := by simpa using hm
      simp only [hm', Bool.false_eq_true, ite_false]
      apply ih (m + 1) _ _ (by omega) (by omega)
      · have := mem_term_step hterm t r m
        rw [show s ^ (m + 1) / ((m + 1).factorial : ℝ) = s ^ m / m.factorial * s / ((m + 1 : ℕ) : ℝ) by
          rw [Nat.factorial_succ]; push_cast; field_simp; ring]
        exact this
      · rw [expPart_succ]; exact Iv.mem_add hs hterm

lemma expSmall_spec (t : ℤ) (r : ℕ) (ht : |(t : ℝ) / 2 ^ (PR + r)| ≤ 1) :
    ivMem (Real.exp ((t : ℝ) / 2 ^ (PR + r))) (W2C.expSmall t r) := by
  have h0 : ivMem (((t : ℝ) / 2 ^ (PR + r)) ^ 0 / (Nat.factorial 0 : ℝ)) (Iv.int 1) := by
    simpa using Iv.mem_int 1
  have hs0 : ivMem (expPart 0 ((t : ℝ) / 2 ^ (PR + r))) ⟨0, 0⟩ := by simp [expPart, ivMem]
  obtain ⟨hsn, hlast⟩ :=
    expTaylorGo_spec t r W2C.EXPN (W2C.EXPN + 1) 0 (Iv.int 1) ⟨0, 0⟩ (by norm_num) (by norm_num) h0 hs0
  have hb := Real.exp_bound ht (n := W2C.EXPN) (by norm_num [W2C.EXPN])
  generalize hres : W2C.expTaylorGo t r W2C.EXPN (W2C.EXPN + 1) 0 (Iv.int 1) ⟨0, 0⟩ = res at hsn hlast
  obtain ⟨sa, last⟩ := res
  simp only at hsn hlast
  generalize hsdef : (t : ℝ) / 2 ^ (PR + r) = s at hsn hlast hb ht ⊢
  have hmag := mag_bound hlast
  have hfac : (0:ℝ) < (W2C.EXPN.factorial : ℝ) := by positivity
  have hpow : |s ^ W2C.EXPN / (W2C.EXPN.factorial : ℝ)| = |s| ^ W2C.EXPN / W2C.EXPN.factorial := by
    rw [abs_div, abs_pow, abs_of_pos hfac]
  rw [hpow] at hmag
  generalize hmagdef : Max.max (Int.natAbs last.lo) (Int.natAbs last.hi) = mag at hmag
  have hrem : |s| ^ W2C.EXPN * ((W2C.EXPN.succ : ℝ) / (W2C.EXPN.factorial * W2C.EXPN : ℝ)) * SC
      ≤ ((divU ((mag : ℤ) * (W2C.EXPN + 1)) W2C.EXPN + 1 : ℤ) : ℝ) := by
    have h2 := le_divU ((mag : ℤ) * (W2C.EXPN + 1)) W2C.EXPN (by norm_num [W2C.EXPN])
    have e : |s| ^ W2C.EXPN * ((W2C.EXPN.succ : ℝ) / (W2C.EXPN.factorial * W2C.EXPN : ℝ)) * SC
        = (|s| ^ W2C.EXPN / W2C.EXPN.factorial * SC) * ((W2C.EXPN : ℝ) + 1) / W2C.EXPN := by
      push_cast; field_simp
    rw [e]
    push_cast at h2 ⊢
    calc (|s| ^ W2C.EXPN / W2C.EXPN.factorial * SC) * ((W2C.EXPN : ℝ) + 1) / W2C.EXPN
        ≤ (mag : ℝ) * ((W2C.EXPN : ℝ) + 1) / W2C.EXPN := by gcongr
      _ ≤ _ := h2
      _ ≤ _ := by linarith
  have heq : W2C.expSmall t r = Iv.widen sa (divU ((mag : ℤ) * (W2C.EXPN + 1)) W2C.EXPN + 1) := by
    unfold W2C.expSmall
    rw [hres, ← hmagdef]
  rw [heq]
  exact mem_widen_of_approx hsn.1 hsn.2 hb hrem

lemma sqrN_spec : ∀ (n : ℕ) {x : ℝ} {a : Iv}, ivMem x a → ivMem (x ^ (2 ^ n)) (W2C.sqrN n a)
  | 0, x, a, h => by simpa [W2C.sqrN] using h
  | n + 1, x, a, h => by
    have h2 := Iv.mem_sqr h
    have := sqrN_spec n h2
    simp only [W2C.sqrN]
    rw [show x ^ 2 ^ (n + 1) = (x ^ 2) ^ 2 ^ n by rw [← pow_mul, pow_succ, mul_comm]]
    exact this

lemma ONE_toNat : ONE.toNat = 2 ^ PR := by unfold ONE PR; norm_num

lemma expShift_spec (t : ℤ) : |(t : ℝ) / 2 ^ (PR + W2C.expShift t)| ≤ 1 := by
  unfold W2C.expShift
  rw [ONE_toNat]
  dsimp only
  have hP : (0:ℝ) < 2 ^ PR := by positivity
  have habs : |(t : ℝ)| = (t.natAbs : ℝ) := by rw [Nat.cast_natAbs]; push_cast; rfl
  split_ifs with h
  · rw [add_zero, abs_div, abs_of_pos hP, habs, div_le_one hP]
    have : (t.natAbs : ℝ) ≤ (2 ^ PR / 2 : ℕ) := by exact_mod_cast h
    have e : ((2 ^ PR / 2 : ℕ) : ℝ) ≤ 2 ^ PR := by
      have : 2 ^ PR / 2 ≤ 2 ^ PR := Nat.div_le_self _ _
      exact_mod_cast this
    linarith
  · set m := t.natAbs
    set q := m / (2 ^ PR / 2)
    have hq : q < 2 ^ (Nat.log2 q + 1) := by
      rw [Nat.log2_eq_log_two]; exact Nat.lt_pow_succ_log_self (by norm_num) q
    have hb : (0 : ℕ) < 2 ^ PR / 2 := by unfold PR; norm_num
    have hm : m < (q + 1) * (2 ^ PR / 2) := by
      have := Nat.lt_div_mul_add (a := m) hb
      rw [show m / (2 ^ PR / 2) * (2 ^ PR / 2) + 2 ^ PR / 2 = (q + 1) * (2 ^ PR / 2) by ring] at this
      exact this
    have hm2 : m < 2 ^ (Nat.log2 q + 1) * (2 ^ PR / 2) :=
      lt_of_lt_of_le hm (Nat.mul_le_mul_right _ hq)
    have e2 : (2 ^ PR / 2 : ℕ) * 2 = 2 ^ PR := by unfold PR; norm_num
    have hpos : (0:ℝ) < 2 ^ (PR + (Nat.log2 q + 1)) := by positivity
    rw [abs_div, abs_of_pos hpos, habs, div_le_one hpos, pow_add]
    have : (m : ℝ) < (2 ^ (Nat.log2 q + 1) * (2 ^ PR / 2) : ℕ) := by exact_mod_cast hm2
    have e3 : ((2 ^ (Nat.log2 q + 1) * (2 ^ PR / 2) : ℕ) : ℝ) ≤ 2 ^ PR * 2 ^ (Nat.log2 q + 1) := by
      have : 2 ^ (Nat.log2 q + 1) * (2 ^ PR / 2) ≤ 2 ^ PR * 2 ^ (Nat.log2 q + 1) := by
        rw [mul_comm]; exact Nat.mul_le_mul_right _ (Nat.div_le_self _ _)
      exact_mod_cast this
    linarith

/-- `exp` at an exact fixed-point number (`|x| ≤ 1024`). -/
theorem expPt_spec (t : ℤ) (ht : t.natAbs ≤ 1024 * ONE.toNat) : ivMem (Real.exp (fx t)) (W2C.expPt t) := by
  unfold W2C.expPt
  simp only [ht, ↓reduceIte]
  set r := W2C.expShift t
  have h1 := expSmall_spec t r (expShift_spec t)
  have h2 := sqrN_spec r h1
  have e : Real.exp ((t : ℝ) / 2 ^ (PR + r)) ^ (2 ^ r) = Real.exp (fx t) := by
    rw [← Real.exp_nat_mul]; congr 1
    unfold fx; rw [pow_add]; push_cast; field_simp
  rw [e] at h2
  obtain ⟨hlo, hhi⟩ := h2
  refine ⟨?_, hhi⟩
  simp only
  rcases le_total (W2C.sqrN r (W2C.expSmall t r)).lo 0 with hc | hc
  · rw [max_eq_right hc]; push_cast; positivity
  · rw [max_eq_left hc]; exact hlo

/-- The lower endpoint of `expPt` is always a lower bound. -/
lemma expPt_lo (t : ℤ) : fx (W2C.expPt t).lo ≤ Real.exp (fx t) := by
  by_cases ht : t.natAbs ≤ 1024 * ONE.toNat
  · exact ivMem_lo_le (expPt_spec t ht)
  · unfold W2C.expPt; simp only [ht, ↓reduceIte]
    rw [show fx 0 = 0 by simp [fx]]; exact (Real.exp_pos _).le

/-- The upper endpoint of `expPt` is an upper bound in range, and for `t ≤ 0`. -/
lemma expPt_hi (t : ℤ) (ht : t.natAbs ≤ 1024 * ONE.toNat ∨ t ≤ 0) : Real.exp (fx t) ≤ fx (W2C.expPt t).hi := by
  by_cases hr : t.natAbs ≤ 1024 * ONE.toNat
  · exact ivMem_hi_le (expPt_spec t hr)
  · have hneg : t ≤ 0 := ht.resolve_left hr
    unfold W2C.expPt; simp only [hr, ↓reduceIte]
    have h1 : Real.exp (fx t) ≤ 1 := by
      rw [Real.exp_le_one_iff]; unfold fx; apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      exact_mod_cast hneg
    have h2 : (1:ℝ) ≤ fx (2 ^ 200) := by unfold fx PR; norm_num
    linarith

lemma firstSome_spec {f : ℤ → Option ℤ} {v : ℤ} (h : W2C.firstSome f = some v) :
    ∃ e, f e = some v := by
  unfold W2C.firstSome at h
  suffices H : ∀ (l : List ℤ) (acc : Option ℤ),
      (acc = none ∨ ∃ e, f e = acc) →
      List.foldl (fun acc e => match acc with | some v => some v | none => f e) acc l = some v →
      ∃ e, f e = some v by
    exact H _ none (Or.inl rfl) h
  intro l
  induction l with
  | nil =>
    intro acc hacc h
    simp only [List.foldl_nil] at h
    rcases hacc with h0 | ⟨e, he⟩
    · rw [h0] at h; exact absurd h (by simp)
    · exact ⟨e, he.trans h⟩
  | cons x xs ih =>
    intro acc hacc h
    simp only [List.foldl_cons] at h
    cases acc with
    | some w => exact ih (some w) hacc h
    | none =>
      cases hfx : f x with
      | none => exact ih none (Or.inl rfl) (by simpa [hfx] using h)
      | some w => exact ih (some w) (Or.inr ⟨x, hfx⟩) (by simpa [hfx] using h)

lemma fx_lt_iff {a b : ℤ} : fx a < fx b ↔ a < b := by
  unfold fx; rw [div_lt_div_iff_of_pos_right (by positivity)]; exact_mod_cast Iff.rfl

/-- `logLo` is a lower bound of `log` (for `a > 0`). -/
theorem logLo_spec (a : ℤ) (ha : 0 < a) : fx (W2C.logLo a) ≤ Real.log (fx a) := by
  have hpos : 0 < fx a := fx_pos_iff.mpr ha
  have hdef : fx (-(2 ^ 200)) ≤ Real.log (fx a) := by
    -- fx a ≥ 2^-96, so log (fx a) ≥ -96 log 2 > -2^104
    have h1 : (2:ℝ)⁻¹ ^ PR ≤ fx a := by
      unfold fx; rw [le_div_iff₀ (by positivity)]
      have : (1:ℝ) ≤ a := by exact_mod_cast ha
      rw [inv_pow, inv_mul_cancel₀ (by positivity)]; exact this
    have h2 : Real.log ((2:ℝ)⁻¹ ^ PR) ≤ Real.log (fx a) := Real.log_le_log (by positivity) h1
    rw [Real.log_pow, Real.log_inv] at h2
    have h3 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    have h4 : fx (-(2 ^ 200)) = -2 ^ 104 := by unfold fx PR; norm_num
    rw [h4]; unfold PR at h2; push_cast at h2; nlinarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)]
  unfold W2C.logLo
  simp only [show ¬ a ≤ 0 by omega, ↓reduceIte]
  cases hfs : W2C.firstSome (fun e =>
      if (W2C.logCand a - e).natAbs ≤ 1024 * ONE.toNat ∧ (W2C.expPt (W2C.logCand a - e)).hi ≤ a
      then some (W2C.logCand a - e) else none) with
  | none => simpa using hdef
  | some θ =>
    simp only [Option.getD_some]
    obtain ⟨e, he⟩ := firstSome_spec hfs
    split_ifs at he with hc
    · simp only [Option.some.injEq] at he
      subst he
      have h1 := expPt_hi _ (Or.inl hc.1)
      have h2 : fx (W2C.expPt (W2C.logCand a - e)).hi ≤ fx a := fx_le_iff.mpr hc.2
      rw [Real.le_log_iff_exp_le hpos]; linarith

/-- `logHi` is an upper bound of `log` (for `0 < a ≤ 2^200`, i.e. `fx a ≤ 2^104`). -/
theorem logHi_spec (a : ℤ) (ha : 0 < a) (ha2 : a ≤ 2 ^ 200) : Real.log (fx a) ≤ fx (W2C.logHi a) := by
  have hpos : 0 < fx a := fx_pos_iff.mpr ha
  have hdef : Real.log (fx a) ≤ fx (2 ^ 200) := by
    have h1 : fx a ≤ fx (2 ^ 200) := fx_le_iff.mpr ha2
    have h2 := Real.log_le_sub_one_of_pos hpos
    linarith
  unfold W2C.logHi
  simp only [show ¬ a ≤ 0 by omega, ↓reduceIte]
  cases hfs : W2C.firstSome (fun e =>
      if a ≤ (W2C.expPt (W2C.logCand a + e)).lo then some (W2C.logCand a + e) else none) with
  | none => simpa using hdef
  | some θ =>
    simp only [Option.getD_some]
    obtain ⟨e, he⟩ := firstSome_spec hfs
    split_ifs at he with hc
    · simp only [Option.some.injEq] at he
      subst he
      have h1 := expPt_lo (W2C.logCand a + e)
      have h2 : fx a ≤ fx (W2C.expPt (W2C.logCand a + e)).lo := fx_le_iff.mpr hc
      rw [Real.log_le_iff_le_exp hpos]; linarith

lemma ivMem_of_fx {x : ℝ} {lo hi : ℤ} (h1 : fx lo ≤ x) (h2 : x ≤ fx hi) : ivMem x ⟨lo, hi⟩ := by
  unfold ivMem fx at *
  have hS : (0:ℝ) < 2 ^ PR := by positivity
  simp only
  constructor
  · rw [div_le_iff₀ hS] at h1; exact h1
  · rw [le_div_iff₀ hS] at h2; exact h2

lemma piLo_lt_seven : piLo.natAbs ≤ 7 * ONE.toNat := by unfold piLo ONE; norm_num
lemma piHi_lt_seven : piHi.natAbs ≤ 7 * ONE.toNat := by unfold piHi ONE; norm_num

lemma natAbs_le_of_bounds {θ : ℤ} (h0 : -piHi ≤ θ) (h1 : θ ≤ piHi) : θ.natAbs ≤ 7 * ONE.toNat := by
  have := piHi_lt_seven
  have hp : 0 ≤ piHi := by unfold piHi; norm_num
  omega

/-- `acosLo` is a lower bound of `arccos`. -/
theorem acosLo_spec (a : ℤ) : fx (W2C.acosLo a) ≤ Real.arccos (fx a) := by
  unfold W2C.acosLo
  dsimp only
  cases hfs : W2C.firstSome (fun e =>
      if W2C.acosCand a - e ≤ 0 then some 0
      else if W2C.acosCand a - e ≤ piLo ∧ a ≤ (cosSin (W2C.acosCand a - e)).1.lo then
        some (W2C.acosCand a - e) else none) with
  | none => simp only [Option.getD_none]; rw [show fx 0 = 0 by simp [fx]]; exact Real.arccos_nonneg _
  | some θ =>
    simp only [Option.getD_some]
    obtain ⟨e, he⟩ := firstSome_spec hfs
    split_ifs at he with h0 hc
    · simp only [Option.some.injEq] at he; subst he
      rw [show fx 0 = 0 by simp [fx]]; exact Real.arccos_nonneg _
    · simp only [Option.some.injEq] at he; subst he
      have hpos : 0 ≤ fx (W2C.acosCand a - e) := fx_nonneg_iff.mpr (by omega)
      have hpi : fx (W2C.acosCand a - e) ≤ π := le_trans (fx_le_iff.mpr hc.1) piLo_le
      have hab : (W2C.acosCand a - e).natAbs ≤ 7 * ONE.toNat :=
        natAbs_le_of_bounds (by have := piHi_lt_seven; unfold piHi at *; omega)
          (le_trans hc.1 (by unfold piLo piHi; norm_num))
      have hcos := (cosSin_sound _ hab).1
      have h1 : fx a ≤ Real.cos (fx (W2C.acosCand a - e)) := le_trans (fx_le_iff.mpr hc.2) (ivMem_lo_le hcos)
      calc fx (W2C.acosCand a - e) = Real.arccos (Real.cos (fx (W2C.acosCand a - e))) :=
            (Real.arccos_cos hpos hpi).symm
        _ ≤ Real.arccos (fx a) := Real.arccos_le_arccos h1

/-- `acosHi` is an upper bound of `arccos`. -/
theorem acosHi_spec (a : ℤ) : Real.arccos (fx a) ≤ fx (W2C.acosHi a) := by
  unfold W2C.acosHi
  dsimp only
  have hdef : Real.arccos (fx a) ≤ fx piHi := le_trans (Real.arccos_le_pi _) le_piHi
  cases hfs : W2C.firstSome (fun e =>
      if piHi ≤ W2C.acosCand a + e then some piHi
      else if 0 ≤ W2C.acosCand a + e ∧ (cosSin (W2C.acosCand a + e)).1.hi ≤ a then
        some (W2C.acosCand a + e) else none) with
  | none => simpa using hdef
  | some θ =>
    simp only [Option.getD_some]
    obtain ⟨e, he⟩ := firstSome_spec hfs
    split_ifs at he with h0 hc
    · simp only [Option.some.injEq] at he; subst he; exact hdef
    · simp only [Option.some.injEq] at he; subst he
      have hpos : 0 ≤ fx (W2C.acosCand a + e) := fx_nonneg_iff.mpr hc.1
      have hab : (W2C.acosCand a + e).natAbs ≤ 7 * ONE.toNat :=
        natAbs_le_of_bounds (by have : (0:ℤ) ≤ piHi := by unfold piHi; norm_num
                                omega) (by omega)
      have hcos := (cosSin_sound _ hab).1
      have h1 : Real.cos (fx (W2C.acosCand a + e)) ≤ fx a := le_trans (ivMem_hi_le hcos) (fx_le_iff.mpr hc.2)
      by_cases hpi : fx (W2C.acosCand a + e) ≤ π
      · calc Real.arccos (fx a) ≤ Real.arccos (Real.cos (fx (W2C.acosCand a + e))) := Real.arccos_le_arccos h1
          _ = fx (W2C.acosCand a + e) := Real.arccos_cos hpos hpi
      · exact le_trans (Real.arccos_le_pi _) (le_of_lt (lt_of_not_ge hpi))

/-- `acosIv` encloses `arccos`. -/
theorem acosIv_spec {x : ℝ} {a : Iv} (h : ivMem x a) : ivMem (Real.arccos x) (W2C.acosIv a) := by
  unfold W2C.acosIv
  apply ivMem_of_fx
  · exact le_trans (acosLo_spec a.hi) (Real.arccos_le_arccos (ivMem_hi_le h))
  · exact le_trans (Real.arccos_le_arccos (ivMem_lo_le h)) (acosHi_spec a.lo)

lemma halfPiLo_le : fx W2C.halfPiLo ≤ π / 2 := by
  have h := piLo_le
  unfold W2C.halfPiLo
  have e : fx (piLo / 2) ≤ fx piLo / 2 := by
    unfold fx
    have : ((piLo / 2 : ℤ) : ℝ) ≤ (piLo : ℝ) / 2 := by
      have := Int.ediv_mul_le piLo (by norm_num : (2:ℤ) ≠ 0)
      have : ((piLo / 2 * 2 : ℤ) : ℝ) ≤ piLo := by exact_mod_cast this
      push_cast at this; linarith
    rw [div_div, mul_comm, ← div_div]; gcongr
  linarith

lemma le_halfPiHi : π / 2 ≤ fx W2C.halfPiHi := by
  have h := le_piHi
  unfold W2C.halfPiHi
  have e : fx piHi / 2 ≤ fx ((piHi + 1) / 2) := by
    unfold fx
    have : (piHi : ℝ) / 2 ≤ (((piHi + 1) / 2 : ℤ) : ℝ) := by
      have := Int.lt_ediv_add_one_mul_self (piHi + 1) (by norm_num : (0:ℤ) < 2)
      have : (piHi + 1 : ℤ) < ((piHi + 1) / 2 + 1) * 2 := this
      have : ((piHi : ℤ) : ℝ) ≤ (((piHi + 1) / 2 : ℤ) : ℝ) * 2 := by
        have : piHi ≤ (piHi + 1) / 2 * 2 := by omega
        exact_mod_cast this
      linarith
    rw [div_div, mul_comm, ← div_div]; gcongr
  linarith

lemma halfPi_natAbs {θ : ℤ} (h0 : -W2C.halfPiLo ≤ θ) (h1 : θ ≤ W2C.halfPiLo) : θ.natAbs ≤ 7 * ONE.toNat := by
  have : W2C.halfPiLo ≤ piHi := by unfold W2C.halfPiLo piLo piHi; norm_num
  exact natAbs_le_of_bounds (by omega) (by omega)

lemma fx_neg (a : ℤ) : fx (-a) = -fx a := by unfold fx; push_cast; ring

/-- `asinLo` is a lower bound of `arcsin`. -/
theorem asinLo_spec (a : ℤ) : fx (W2C.asinLo a) ≤ Real.arcsin (fx a) := by
  unfold W2C.asinLo
  dsimp only
  have hdef : fx (-W2C.halfPiHi) ≤ Real.arcsin (fx a) := by
    rw [fx_neg]; linarith [le_halfPiHi, Real.neg_pi_div_two_le_arcsin (fx a)]
  cases hfs : W2C.firstSome (fun e =>
      if W2C.asinCand a - e ≤ -W2C.halfPiHi then some (-W2C.halfPiHi)
      else if -W2C.halfPiLo ≤ W2C.asinCand a - e ∧ W2C.asinCand a - e ≤ W2C.halfPiLo ∧
          (cosSin (W2C.asinCand a - e)).2.hi ≤ a then some (W2C.asinCand a - e) else none) with
  | none => simpa using hdef
  | some θ =>
    simp only [Option.getD_some]
    obtain ⟨e, he⟩ := firstSome_spec hfs
    split_ifs at he with h0 hc
    · simp only [Option.some.injEq] at he; subst he; exact hdef
    · simp only [Option.some.injEq] at he; subst he
      have hsin := (cosSin_sound _ (halfPi_natAbs hc.1 hc.2.1)).2
      have h1 : Real.sin (fx (W2C.asinCand a - e)) ≤ fx a := le_trans (ivMem_hi_le hsin) (fx_le_iff.mpr hc.2.2)
      have hlo : -(π / 2) ≤ fx (W2C.asinCand a - e) := by
        have := fx_le_iff.mpr hc.1; rw [fx_neg] at this; linarith [halfPiLo_le]
      have hhi : fx (W2C.asinCand a - e) ≤ π / 2 := le_trans (fx_le_iff.mpr hc.2.1) halfPiLo_le
      calc fx (W2C.asinCand a - e) = Real.arcsin (Real.sin (fx (W2C.asinCand a - e))) :=
            (Real.arcsin_sin hlo hhi).symm
        _ ≤ Real.arcsin (fx a) := Real.arcsin_le_arcsin h1

/-- `asinHi` is an upper bound of `arcsin`. -/
theorem asinHi_spec (a : ℤ) : Real.arcsin (fx a) ≤ fx (W2C.asinHi a) := by
  unfold W2C.asinHi
  dsimp only
  have hdef : Real.arcsin (fx a) ≤ fx W2C.halfPiHi := le_trans (Real.arcsin_le_pi_div_two _) le_halfPiHi
  cases hfs : W2C.firstSome (fun e =>
      if W2C.halfPiHi ≤ W2C.asinCand a + e then some W2C.halfPiHi
      else if -W2C.halfPiLo ≤ W2C.asinCand a + e ∧ W2C.asinCand a + e ≤ W2C.halfPiLo ∧
          a ≤ (cosSin (W2C.asinCand a + e)).2.lo then some (W2C.asinCand a + e) else none) with
  | none => simpa using hdef
  | some θ =>
    simp only [Option.getD_some]
    obtain ⟨e, he⟩ := firstSome_spec hfs
    split_ifs at he with h0 hc
    · simp only [Option.some.injEq] at he; subst he; exact hdef
    · simp only [Option.some.injEq] at he; subst he
      have hsin := (cosSin_sound _ (halfPi_natAbs hc.1 hc.2.1)).2
      have h1 : fx a ≤ Real.sin (fx (W2C.asinCand a + e)) := le_trans (fx_le_iff.mpr hc.2.2) (ivMem_lo_le hsin)
      have hlo : -(π / 2) ≤ fx (W2C.asinCand a + e) := by
        have := fx_le_iff.mpr hc.1; rw [fx_neg] at this; linarith [halfPiLo_le]
      have hhi : fx (W2C.asinCand a + e) ≤ π / 2 := le_trans (fx_le_iff.mpr hc.2.1) halfPiLo_le
      calc Real.arcsin (fx a) ≤ Real.arcsin (Real.sin (fx (W2C.asinCand a + e))) := Real.arcsin_le_arcsin h1
        _ = fx (W2C.asinCand a + e) := Real.arcsin_sin hlo hhi

/-- `asinIv` encloses `arcsin`. -/
theorem asinIv_spec {x : ℝ} {a : Iv} (h : ivMem x a) : ivMem (Real.arcsin x) (W2C.asinIv a) := by
  unfold W2C.asinIv
  apply ivMem_of_fx
  · exact le_trans (asinLo_spec a.lo) (Real.arcsin_le_arcsin (ivMem_lo_le h))
  · exact le_trans (Real.arcsin_le_arcsin (ivMem_hi_le h)) (asinHi_spec a.hi)

end BHH.W2
