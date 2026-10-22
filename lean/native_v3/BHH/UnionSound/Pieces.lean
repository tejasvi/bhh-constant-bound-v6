/-
Module B (union area), part 2: proxy pieces.

`ArcFor A ar` says that the code's arc `ar` is a proxy for the (2π-periodic, measurable) covered set `A`: there are
reals `a < c`, `d < b` with `I = [c, d] ⊆ A`, `A ⊆ U = (a, b)` mod `2π`, the proxy endpoints between `U` and `I`
with margin `2 piErr`, and `|U \ I| = (c - a) + (b - d) ≤ slack`.  A certified arc (`ArcCert`) gives `ArcFor` for the
covered set on its own circle and, shifted by `π`, on the other circle.  `normArc_spec`: the pieces of `normArc` lie
in `U` mod `2π`, and every point of `I` is (mod `2π`) inside a piece or congruent to `0`.
-/
import BHH.UnionSound.Arc

open BHH.Cert Real Set

namespace BHH

noncomputable section

namespace US

/-! ## direction points: ranges, values, valid enclosures -/

/-- `p` is the top `2π`, or an exact point in `[0, 2 piLo]` -/
def InRange (p : DirPt) : Prop := p.top = true ∨ (p.top = false ∧ 0 ≤ p.t ∧ p.t ≤ 2 * piLo)

lemma fx_two_mul (a : ℤ) : fx (2 * a) = 2 * fx a := by simp only [fx_eq]; push_cast; ring

lemma two_pL_lt : 2 * pL < 2 * π := by linarith [pL_lt_pi]

lemma dval_top {p : DirPt} (h : p.top = true) : dval p = 2 * π := by simp [dval, h]

lemma dval_mem {p : DirPt} (h : InRange p) : 0 ≤ dval p ∧ dval p ≤ 2 * π := by
  rcases h with h | ⟨h, h1, h2⟩
  · rw [dval_top h]; constructor <;> linarith [Real.pi_pos]
  · rw [dval_of_not_top h]
    have a1 : 0 ≤ fx p.t := fx_nonneg_iff.mpr h1
    have a2 : fx p.t ≤ fx (2 * piLo) := fx_le_iff.mpr h2
    rw [fx_two_mul, fx_piLo] at a2
    constructor <;> linarith [two_pL_lt]

lemma dval_lt_of_not_top {p : DirPt} (h : InRange p) (ht : p.top = false) : dval p < 2 * π := by
  rcases h with h | ⟨_, _, h2⟩
  · rw [h] at ht; exact absurd ht (by decide)
  · rw [dval_of_not_top ht]
    have a2 : fx p.t ≤ fx (2 * piLo) := fx_le_iff.mpr h2
    rw [fx_two_mul, fx_piLo] at a2
    linarith [two_pL_lt]

lemma dirLe_iff {p q : DirPt} (hp : InRange p) (hq : InRange q) : dirLe p q = true ↔ dval p ≤ dval q := by
  unfold dirLe
  cases hqt : q.top
  · cases hpt : p.top
    · simp only [Bool.false_eq_true, ite_false, decide_eq_true_eq]
      rw [dval_of_not_top hpt, dval_of_not_top hqt, fx_le_iff]
    · simp only [Bool.false_eq_true, ite_false, ite_true]
      rw [dval_top hpt]
      have := dval_lt_of_not_top hq hqt
      constructor
      · intro h; exact absurd h (by decide)
      · intro h; linarith
  · simp only [ite_true, true_iff]
    rw [dval_top hqt]; exact (dval_mem hp).2

/-- an enclosure of `y`, widened by `w ≥ |x - y|`, encloses `x` -/
lemma mem_widen_of_near {x y : ℝ} {a : Iv} {w : ℤ} (hy : ivMem y a) (hxy : |x - y| ≤ fx w) :
    ivMem x (Iv.widen a w) := by
  obtain ⟨h1, h2⟩ := hy
  have hS : (0 : ℝ) < 2 ^ PR := by positivity
  obtain ⟨k1, k2⟩ := abs_le.mp hxy
  have hw : (w : ℝ) = fx w * 2 ^ PR := by rw [fx]; field_simp
  unfold ivMem Iv.widen; simp only; push_cast
  constructor <;> nlinarith

lemma cos_near {x δ δ' : ℝ} : |Real.cos (x + δ) - Real.cos (x + δ')| ≤ |δ - δ'| := by
  have := Real.abs_cos_sub_cos_le (x + δ) (x + δ')
  rwa [show x + δ - (x + δ') = δ - δ' by ring] at this

lemma sin_near {x δ δ' : ℝ} : |Real.sin (x + δ) - Real.sin (x + δ')| ≤ |δ - δ'| := by
  have := Real.abs_sin_sub_sin_le (x + δ) (x + δ')
  rwa [show x + δ - (x + δ') = δ - δ' by ring] at this

lemma abs_two_pX_sub (up : Bool) : |2 * (if up then pH else pL) - 2 * π| ≤ 2 * pE := by
  have := pi_sub_pL_lt; have := pH_sub_pi_lt; have := pL_lt_pi; have := pi_lt_pH
  cases up
  · simp only [Bool.false_eq_true, ite_false]; rw [abs_le]; constructor <;> linarith
  · simp only [ite_true]; rw [abs_le]; constructor <;> linarith

lemma abs_pX_sub (up : Bool) : |(if up then pH else pL) - π| ≤ pE := by
  have := pi_sub_pL_lt; have := pH_sub_pi_lt; have := pL_lt_pi; have := pi_lt_pH
  cases up
  · simp only [Bool.false_eq_true, ite_false]; rw [abs_le]; constructor <;> linarith
  · simp only [ite_true]; rw [abs_le]; constructor <;> linarith

lemma fx_two_piErr : fx (2 * piErr) = 2 * pE := by rw [fx_two_mul]; rfl

@[simp] lemma shift2Pi_top (p : DirPt) (up : Bool) : (shift2Pi p up).top = false := rfl
@[simp] lemma unshift2Pi_top (p : DirPt) (up : Bool) : (unshift2Pi p up).top = false := rfl
@[simp] lemma shiftPi_top (p : DirPt) (up : Bool) : (shiftPi p up).top = false := rfl
@[simp] lemma shift2Pi_t (p : DirPt) (up : Bool) :
    (shift2Pi p up).t = p.t + 2 * (if up then piHi else piLo) := rfl
@[simp] lemma unshift2Pi_t (p : DirPt) (up : Bool) :
    (unshift2Pi p up).t = p.t - 2 * (if up then piLo else piHi) := rfl
@[simp] lemma shiftPi_t (p : DirPt) (up : Bool) : (shiftPi p up).t = p.t + (if up then piHi else piLo) := rfl

lemma dval_shift2Pi (p : DirPt) (up : Bool) :
    dval (shift2Pi p up) = fx p.t + 2 * (if up then pH else pL) := by
  rw [dval_of_not_top (shift2Pi_top p up)]
  simp only [shift2Pi, fx_add, fx_two_mul]
  cases up <;> rfl

lemma dval_unshift2Pi (p : DirPt) (up : Bool) :
    dval (unshift2Pi p up) = fx p.t - 2 * (if up then pL else pH) := by
  rw [dval_of_not_top (unshift2Pi_top p up)]
  simp only [unshift2Pi, fx_sub, fx_two_mul]
  cases up <;> rfl

lemma dval_shiftPi (p : DirPt) (up : Bool) : dval (shiftPi p up) = fx p.t + (if up then pH else pL) := by
  rw [dval_of_not_top (shiftPi_top p up)]
  simp only [shiftPi, fx_add]
  cases up <;> rfl

lemma dval_dirZero : dval dirZero = 0 := by simp [dval, dirZero, fx_zero]
lemma dval_dirTop : dval dirTop = 2 * π := by simp [dval, dirTop]

lemma DirOK_shift2Pi {p : DirPt} (hp : p.top = false) (h : DirOK p) (up : Bool) : DirOK (shift2Pi p up) := by
  unfold DirOK at h ⊢
  rw [dval_of_not_top hp] at h
  rw [dval_shift2Pi]
  have hb := abs_two_pX_sub up
  constructor
  · apply mem_widen_of_near h.1
    rw [fx_two_piErr]
    have := cos_near (x := fx p.t) (δ := 2 * (if up then pH else pL)) (δ' := 2 * π)
    rw [Real.cos_add_two_pi] at this
    linarith
  · apply mem_widen_of_near h.2
    rw [fx_two_piErr]
    have := sin_near (x := fx p.t) (δ := 2 * (if up then pH else pL)) (δ' := 2 * π)
    rw [Real.sin_add_two_pi] at this
    linarith

lemma DirOK_unshift2Pi {p : DirPt} (hp : p.top = false) (h : DirOK p) (up : Bool) :
    DirOK (unshift2Pi p up) := by
  unfold DirOK at h ⊢
  rw [dval_of_not_top hp] at h
  rw [dval_unshift2Pi]
  have hb : |-(2 * (if up then pL else pH)) - -(2 * π)| ≤ 2 * pE := by
    have := pi_sub_pL_lt; have := pH_sub_pi_lt; have := pL_lt_pi; have := pi_lt_pH
    cases up
    · simp only [Bool.false_eq_true, ite_false]; rw [abs_le]; constructor <;> linarith
    · simp only [ite_true]; rw [abs_le]; constructor <;> linarith
  constructor
  · apply mem_widen_of_near h.1
    rw [fx_two_piErr]
    have := cos_near (x := fx p.t) (δ := -(2 * (if up then pL else pH))) (δ' := -(2 * π))
    rw [← sub_eq_add_neg, ← sub_eq_add_neg, Real.cos_sub_two_pi] at this
    linarith
  · apply mem_widen_of_near h.2
    rw [fx_two_piErr]
    have := sin_near (x := fx p.t) (δ := -(2 * (if up then pL else pH))) (δ' := -(2 * π))
    rw [← sub_eq_add_neg, ← sub_eq_add_neg, Real.sin_sub_two_pi] at this
    linarith

lemma DirOK_shiftPi {p : DirPt} (hp : p.top = false) (h : DirOK p) (up : Bool) : DirOK (shiftPi p up) := by
  unfold DirOK at h ⊢
  rw [dval_of_not_top hp] at h
  rw [dval_shiftPi]
  have hb := abs_pX_sub up
  constructor
  · apply mem_widen_of_near (Iv.mem_neg h.1)
    show _ ≤ pE
    have := cos_near (x := fx p.t) (δ := (if up then pH else pL)) (δ' := π)
    rw [Real.cos_add_pi] at this
    linarith
  · apply mem_widen_of_near (Iv.mem_neg h.2)
    show _ ≤ pE
    have := sin_near (x := fx p.t) (δ := (if up then pH else pL)) (δ' := π)
    rw [Real.sin_add_pi] at this
    linarith

lemma DirOK_dirZero : DirOK dirZero := by
  unfold DirOK; rw [dval_dirZero, Real.cos_zero, Real.sin_zero]
  have h1 := Iv.mem_int 1; have h0 := Iv.mem_int 0
  rw [Int.cast_one] at h1; rw [Int.cast_zero] at h0
  exact ⟨h1, h0⟩

lemma DirOK_dirTop : DirOK dirTop := by
  unfold DirOK; rw [dval_dirTop, Real.cos_two_pi, Real.sin_two_pi]
  have h1 := Iv.mem_int 1; have h0 := Iv.mem_int 0
  rw [Int.cast_one] at h1; rw [Int.cast_zero] at h0
  exact ⟨h1, h0⟩

lemma InRange_dirZero : InRange dirZero := Or.inr ⟨rfl, le_refl _, show (0 : ℤ) ≤ 2 * piLo by norm_num [piLo]⟩
lemma InRange_dirTop : InRange dirTop := Or.inl rfl

/-! ## arcs as proxies of covered sets -/

/-- The code's arc `ar` is a proxy for the covered set `A` (see the file header). -/
def ArcFor (A : Set ℝ) (ar : Arc) : Prop :=
  ∃ a c d b : ℝ,
    ar.s.top = false ∧ ar.e.top = false ∧ DirOK ar.s ∧ DirOK ar.e ∧
    -(2 * piLo) ≤ ar.s.t ∧ ar.s.t ≤ 2 * piLo ∧ ar.s.t < ar.e.t ∧ ar.e.t - ar.s.t < 2 * piLo ∧
    a + 2 * pE < fx ar.s.t ∧ fx ar.s.t < c ∧ d < fx ar.e.t ∧ fx ar.e.t + 2 * pE < b ∧
    (c - a) + (b - d) ≤ fx ar.slack ∧
    MeasurableSet A ∧
    (∀ t ∈ Icc c d, t ∈ A) ∧
    (∀ t ∈ A, ∃ n : ℤ, t + n * (2 * π) ∈ Ioo a b) ∧
    (∀ t (n : ℤ), t ∈ A → t + n * (2 * π) ∈ A)

lemma Gf_continuous (ρ wx wy d : ℝ) : Continuous (Gf ρ wx wy d) := by
  unfold Gf; fun_prop

lemma Gf_sub_pi (ρ wx wy d t : ℝ) : Gf ρ wx wy d (t - π) = Gf ρ (-wx) (-wy) d t := by
  simp only [Gf, Real.cos_sub_pi, Real.sin_sub_pi]; ring

/-- A certified arc is a proxy of the covered set on its own circle. -/
theorem arcFor_of_cert {ρ wx wy d : ℝ} (hd : 0 < d) {ar : Arc} (h : ArcCert (Gf ρ wx wy d) ar) :
    ArcFor {t | 0 < Gf ρ wx wy d t} ar := by
  obtain ⟨e, he1, he2, hsl, hst, het, hs1, hs2, hse, hw, hsok, heok, g1, g2, g3, g4⟩ := h
  have hε : 4 * pE ≤ fx e := by
    have := fx_le_iff.mpr he1; rwa [fx_mul_int, fx_piErr] at this
  have hpE := pE_pos
  have hσ : fx ar.s.t + fx e ≤ fx ar.e.t - fx e := by
    have := fx_le_iff.mpr hse; rwa [fx_add, fx_sub] at this
  have hwr : (fx ar.e.t + fx e) - (fx ar.s.t - fx e) < pL := by
    have := fx_lt_iff.mpr hw; rwa [fx_sub, fx_add, fx_sub] at this
  have hpL := pL_lt_pi
  have he0 : 0 < e := lt_of_lt_of_le (by norm_num [piErr, piHi, piLo]) he1
  refine ⟨fx ar.s.t - fx e, fx ar.s.t + fx e, fx ar.e.t - fx e, fx ar.e.t + fx e, hst, het, hsok, heok,
    hs1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans hs2 (by norm_num [piLo])
  · linarith
  · have : piLo ≤ 2 * piLo := by norm_num [piLo]
    linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · rw [hsl, fx_mul_int]; push_cast; linarith
  · exact measurableSet_lt measurable_const (Gf_continuous ρ wx wy d).measurable
  · intro t ht
    exact arc_pos hd ht.1 ht.2 (by linarith) g2 g3
  · intro t ht
    exact arc_in hd (c := fx ar.s.t + fx e) (by linarith) (by linarith) g1 g4 g2 ht
  · intro t n ht
    show 0 < Gf ρ wx wy d (t + n * (2 * π))
    rw [Gf_add_int_mul_two_pi]; exact ht

/-- the arc on the other circle -/
def shiftArc (ar : Arc) : Arc := ⟨shiftPi ar.s false, shiftPi ar.e true, ar.slack⟩

/-- A certified arc, shifted by `π`, is a proxy of the covered set on the other circle. -/
theorem arcFor_shift_of_cert {ρ wx wy d : ℝ} (hd : 0 < d) {ar : Arc} (h : ArcCert (Gf ρ wx wy d) ar) :
    ArcFor {t | 0 < Gf ρ wx wy d (t - π)} (shiftArc ar) := by
  have hA := arcFor_of_cert hd h
  obtain ⟨e, he1, he2, hsl, hst, het, hs1, hs2, hse, hw, hsok, heok, g1, g2, g3, g4⟩ := h
  obtain ⟨a, c, d', b, -, -, -, -, -, -, -, -, -, -, -, -, -, hmeas, hI, hU, hper⟩ := hA
  have hε : 4 * pE ≤ fx e := by
    have := fx_le_iff.mpr he1; rwa [fx_mul_int, fx_piErr] at this
  have hpE := pE_pos
  have hσ : fx ar.s.t + fx e ≤ fx ar.e.t - fx e := by
    have := fx_le_iff.mpr hse; rwa [fx_add, fx_sub] at this
  have hpL := pL_lt_pi
  have hpH := pi_lt_pH
  have hpLE := pi_sub_pL_lt
  have hpHE := pH_sub_pi_lt
  have he0 : 0 < e := lt_of_lt_of_le (by norm_num [piErr, piHi, piLo]) he1
  have hsl' : fx ar.slack = 4 * fx e := by rw [hsl, fx_mul_int]; push_cast; ring
  have hpp : piLo < piHi := by norm_num [piLo, piHi]
  have e1 : (shiftArc ar).s.t = ar.s.t + piLo := rfl
  have e2 : (shiftArc ar).e.t = ar.e.t + piHi := rfl
  have e3 : (shiftArc ar).slack = ar.slack := rfl
  refine ⟨fx ar.s.t + π - fx e, fx ar.s.t + π + fx e, fx ar.e.t + π - fx e, fx ar.e.t + π + fx e,
    rfl, rfl, DirOK_shiftPi hst hsok false, DirOK_shiftPi het heok true, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [e1]; linarith
  · rw [e1]; linarith
  · rw [e1, e2]; linarith
  · rw [e1, e2]
    have : piHi - piLo < piLo := by norm_num [piHi, piLo]
    linarith
  · rw [e1, fx_add, fx_piLo]; linarith
  · rw [e1, fx_add, fx_piLo]; linarith
  · rw [e2, fx_add, fx_piHi]; linarith
  · rw [e2, fx_add, fx_piHi]; linarith
  · rw [e3, hsl']; linarith
  · exact measurableSet_lt measurable_const
      ((Gf_continuous ρ wx wy d).comp (continuous_id.sub continuous_const)).measurable
  · intro t ht
    show 0 < Gf ρ wx wy d (t - π)
    exact arc_pos hd (p := fx ar.s.t + fx e) (q := fx ar.e.t - fx e) (by linarith [ht.1]) (by linarith [ht.2])
      (by have := fx_lt_iff.mpr hw; rw [fx_sub, fx_add, fx_sub, fx_piLo] at this; linarith) g2 g3
  · intro t ht
    have ht' : 0 < Gf ρ wx wy d (t - π) := ht
    obtain ⟨n, hn1, hn2⟩ := arc_in hd (a := fx ar.s.t - fx e) (b := fx ar.e.t + fx e)
      (c := fx ar.s.t + fx e) (by linarith) (by linarith) g1 g4 g2 ht'
    exact ⟨n, by linarith, by linarith⟩
  · intro t n ht
    show 0 < Gf ρ wx wy d (t + n * (2 * π) - π)
    rw [show t + n * (2 * π) - π = (t - π) + n * (2 * π) by ring, Gf_add_int_mul_two_pi]
    exact ht

/-! ## `normArc` -/

/-- The pieces of `normArc s e` (for an arc `(s, e)` with the margins of `ArcFor`) lie in `U` mod `2π`, and every
point of `I` is mod `2π` inside a piece (open) or congruent to `0`. -/
theorem normArc_spec {s e : DirPt} {a c d b : ℝ}
    (hst : s.top = false) (het : e.top = false) (hs : DirOK s) (he : DirOK e)
    (h1 : -(2 * piLo) ≤ s.t) (h2 : s.t ≤ 2 * piLo) (h3 : s.t < e.t) (h4 : e.t - s.t < 2 * piLo)
    (ha : a + 2 * pE < fx s.t) (hc : fx s.t < c) (hd : d < fx e.t) (hb : fx e.t + 2 * pE < b) :
    (∀ pc ∈ normArc s e, pc.a.top = false ∧ InRange pc.a ∧ InRange pc.b ∧ DirOK pc.a ∧ DirOK pc.b) ∧
    (∀ pc ∈ normArc s e, ∀ t ∈ Icc (dval pc.a) (dval pc.b), ∃ n : ℤ, t + n * (2 * π) ∈ Ioo a b) ∧
    (∀ x ∈ Icc c d, (∃ m : ℤ, x + m * (2 * π) = 0) ∨
      ∃ pc ∈ normArc s e, ∃ m : ℤ, x + m * (2 * π) ∈ Ioo (dval pc.a) (dval pc.b)) := by
  have hpL := pL_lt_pi
  have hpH := pi_lt_pH
  have hpLE := pi_sub_pL_lt
  have hpHE := pH_sub_pi_lt
  have hpE := pE_pos
  have hpEeq := pE_eq
  have h3pL := three_lt_pL
  have hpp : piLo ≤ piHi := by norm_num [piLo, piHi]
  have hpos : 0 < piLo := by norm_num [piLo]
  -- real forms of the integer data
  have r1 : -(2 * pL) ≤ fx s.t := by
    have := fx_le_iff.mpr h1; rwa [fx_neg, fx_two_mul, fx_piLo] at this
  have r2 : fx s.t ≤ 2 * pL := by
    have := fx_le_iff.mpr h2; rwa [fx_two_mul, fx_piLo] at this
  have r3 : fx s.t < fx e.t := fx_lt_iff.mpr h3
  have r4 : fx e.t - fx s.t < 2 * pL := by
    have := fx_lt_iff.mpr h4; rwa [fx_sub, fx_two_mul, fx_piLo] at this
  have hsv := dval_of_not_top hst
  have hev := dval_of_not_top het
  have hs2' : dval (shift2Pi s false) = fx s.t + 2 * pL := by rw [dval_shift2Pi]; rfl
  have he2' : dval (shift2Pi e true) = fx e.t + 2 * pH := by rw [dval_shift2Pi]; rfl
  have heu' : dval (unshift2Pi e true) = fx e.t - 2 * pL := by rw [dval_unshift2Pi]; rfl
  have hz := dval_dirZero
  have htop := dval_dirTop
  unfold normArc
  split_ifs with b1 b2 b3 b4 b5 b6 b7 b8
  · -- s.t + 2 piLo < 0: excluded
    exfalso; linarith
  · -- e.t ≤ 0, e.t + 2 piHi ≤ 2 piLo: one shifted piece
    have r5 : fx e.t + 2 * pH ≤ 2 * pL := by
      have := fx_le_iff.mpr b4; rwa [fx_add, fx_two_mul, fx_two_mul, fx_piHi, fx_piLo] at this
    have r6 : fx e.t ≤ 0 := by have := fx_le_iff.mpr b3; rwa [fx_zero] at this
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.mem_singleton, forall_eq]
      refine ⟨rfl, Or.inr ⟨rfl, ?_, ?_⟩, Or.inr ⟨rfl, ?_, ?_⟩, DirOK_shift2Pi hst hs false,
        DirOK_shift2Pi het he true⟩ <;> simp only [shift2Pi_t, Bool.false_eq_true, ite_false, ite_true] <;> omega
    · simp only [List.mem_singleton, forall_eq]
      rw [hs2', he2']
      intro t ht
      exact ⟨-1, by push_cast; linarith [ht.1], by push_cast; linarith [ht.2]⟩
    · intro x hx
      right
      refine ⟨_, List.mem_singleton_self _, 1, ?_, ?_⟩
      · simp only [hs2']; push_cast; linarith [hx.1]
      · simp only [he2']; push_cast; linarith [hx.2]
  · -- e.t ≤ 0, e.t + 2 piHi > 2 piLo: shifted start to the top
    have r5 : 2 * pL < fx e.t + 2 * pH := by
      have := fx_lt_iff.mpr (lt_of_not_ge b4); rwa [fx_add, fx_two_mul, fx_two_mul, fx_piHi, fx_piLo] at this
    have r6 : fx e.t ≤ 0 := by have := fx_le_iff.mpr b3; rwa [fx_zero] at this
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.mem_singleton, forall_eq]
      refine ⟨rfl, Or.inr ⟨rfl, ?_, ?_⟩, InRange_dirTop, DirOK_shift2Pi hst hs false, DirOK_dirTop⟩ <;>
        simp only [shift2Pi_t, Bool.false_eq_true, ite_false] <;> omega
    · simp only [List.mem_singleton, forall_eq]
      rw [hs2', htop]
      intro t ht
      exact ⟨-1, by push_cast; linarith [ht.1], by push_cast; linarith [ht.2]⟩
    · intro x hx
      right
      refine ⟨_, List.mem_singleton_self _, 1, ?_, ?_⟩
      · simp only [hs2']; push_cast; linarith [hx.1]
      · simp only [htop]; push_cast; linarith [hx.2]
  · -- 0 < e.t ≤ 2 piLo: two pieces
    have r6 : 0 < fx e.t := by have := fx_lt_iff.mpr (lt_of_not_ge b3); rwa [fx_zero] at this
    have r7 : fx e.t ≤ 2 * pL := by
      have := fx_le_iff.mpr b5; rwa [fx_two_mul, fx_piLo] at this
    have r8 : fx s.t < 0 := by have := fx_lt_iff.mpr b1; rwa [fx_zero] at this
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      refine ⟨⟨rfl, Or.inr ⟨rfl, ?_, ?_⟩, InRange_dirTop, DirOK_shift2Pi hst hs false, DirOK_dirTop⟩,
        ⟨rfl, InRange_dirZero, Or.inr ⟨het, by omega, b5⟩, DirOK_dirZero, he⟩⟩ <;>
        simp only [shift2Pi_t, Bool.false_eq_true, ite_false] <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      constructor
      · rw [hs2', htop]
        intro t ht
        exact ⟨-1, by push_cast; linarith [ht.1], by push_cast; linarith [ht.2]⟩
      · rw [hz, hev]
        intro t ht
        exact ⟨0, by push_cast; linarith [ht.1], by push_cast; linarith [ht.2]⟩
    · intro x hx
      rcases lt_trichotomy x 0 with hx0 | hx0 | hx0
      · right
        refine ⟨⟨shift2Pi s false, dirTop⟩, by simp, 1, ?_, ?_⟩
        · simp only [hs2']; push_cast; linarith [hx.1]
        · simp only [htop]; push_cast; linarith
      · left; exact ⟨0, by rw [hx0]; push_cast; ring⟩
      · right
        refine ⟨⟨dirZero, e⟩, by simp, 0, ?_, ?_⟩
        · simp only [hz]; push_cast; linarith
        · simp only [hev]; push_cast; linarith [hx.2]
  · -- excluded: s.t < 0 < 2 piLo < e.t
    exfalso; omega
  · -- 0 ≤ s.t, e.t ≤ 2 piLo: one piece
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.mem_singleton, forall_eq]
      exact ⟨hst, Or.inr ⟨hst, by omega, by omega⟩, Or.inr ⟨het, by omega, b6⟩, hs, he⟩
    · simp only [List.mem_singleton, forall_eq]
      rw [hsv, hev]
      intro t ht
      exact ⟨0, by push_cast; linarith [ht.1], by push_cast; linarith [ht.2]⟩
    · intro x hx
      right
      refine ⟨_, List.mem_singleton_self _, 0, ?_, ?_⟩
      · simp only [hsv]; push_cast; linarith [hx.1]
      · simp only [hev]; push_cast; linarith [hx.2]
  · -- 0 ≤ s.t, 2 piLo < e.t ≤ 4 piLo: two pieces across 2π
    have b9 : s.t ≤ 2 * piLo := h2
    have r6 : 2 * pL < fx e.t := by
      have := fx_lt_iff.mpr (lt_of_not_ge b6); rwa [fx_two_mul, fx_piLo] at this
    have r9 : 0 ≤ fx s.t := by have := fx_le_iff.mpr (le_of_not_gt b1); rwa [fx_zero] at this
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      refine ⟨⟨hst, Or.inr ⟨hst, by omega, b9⟩, InRange_dirTop, hs, DirOK_dirTop⟩,
        ⟨rfl, InRange_dirZero, Or.inr ⟨rfl, ?_, ?_⟩, DirOK_dirZero, DirOK_unshift2Pi het he true⟩⟩
      · simp only [unshift2Pi_t, ite_true]; omega
      · simp only [unshift2Pi_t, ite_true]; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      constructor
      · rw [hsv, htop]
        intro t ht
        exact ⟨0, by push_cast; linarith [ht.1], by push_cast; linarith [ht.2]⟩
      · rw [hz, heu']
        intro t ht
        exact ⟨1, by push_cast; linarith [ht.1], by push_cast; linarith [ht.2]⟩
    · intro x hx
      rcases lt_trichotomy x (2 * π) with hx0 | hx0 | hx0
      · right
        refine ⟨⟨s, dirTop⟩, by simp, 0, ?_, ?_⟩
        · simp only [hsv]; push_cast; linarith [hx.1]
        · simp only [htop]; push_cast; linarith
      · left; exact ⟨-1, by rw [hx0]; push_cast; ring⟩
      · right
        refine ⟨⟨dirZero, unshift2Pi e true⟩, by simp, -1, ?_, ?_⟩
        · simp only [hz]; push_cast; linarith
        · simp only [heu']; push_cast; linarith [hx.2]
  · -- excluded: e.t > 4 piLo
    exfalso; omega

end US

end

end BHH
