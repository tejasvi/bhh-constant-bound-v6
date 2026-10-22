/-
Module B (union area), part 1: certified arcs.

For the circle around `c_i` (radius `ρ`) and the disk around `c_j` (`w = c_j - c_i`, `d = |w|²`), the directions
`t` with `c_i + ρ u(t)` in the open disk `B°(c_j, ρ)` are those with `G(t) = 2ρ⟨u(t), w⟩ - d > 0`.  This file proves
* the arc lemmas: if `G > 0` at both ends of an interval of length `< π`, then on the whole interval (`arc_pos`); if
  `G < 0` at both ends of an interval `(a, b)` of length `< π` and `G > 0` somewhere inside, then every `t` with
  `G(t) > 0` is congruent mod `2π` to a point of `(a, b)` (`arc_in`);
* soundness of `certArcWith` and `certArc`: a returned arc satisfies `ArcCert G` (the four signs of `G` at
  `θ_L ± ε`, `θ_H ± ε`, the ranges of `θ_L`, `θ_H`, `ε`, and valid cos/sin enclosures at the endpoints).
-/
import BHH.Ivl.Basic

open BHH.Cert Real Set

namespace BHH

noncomputable section

namespace US

/-! ## π -/

/-- `piLo / 2^PR` -/
abbrev pL : ℝ := (piLo : ℝ) / SC
/-- `piHi / 2^PR` -/
abbrev pH : ℝ := (piHi : ℝ) / SC
/-- `piErr / 2^PR` -/
abbrev pE : ℝ := (piErr : ℝ) / SC

lemma pL_lt_pi : pL < π := by
  have h := Real.pi_gt_d20
  have : (piLo : ℝ) / SC ≤ 3.14159265358979323846 := by
    rw [div_le_iff₀ SC_pos]; simp only [SC, PR, piLo]; norm_num
  exact lt_of_le_of_lt this h

lemma pi_lt_pH : π < pH := by
  have h := Real.pi_lt_d20
  have : (3.14159265358979323847 : ℝ) ≤ (piHi : ℝ) / SC := by
    rw [le_div_iff₀ SC_pos]; simp only [SC, PR, piHi]; norm_num
  exact lt_of_lt_of_le h this

lemma pE_eq : pE = pH - pL := by
  simp only [pE, pH, pL, piErr]; push_cast; ring

lemma pE_pos : 0 < pE := by have := pL_lt_pi; have := pi_lt_pH; rw [pE_eq]; linarith

lemma pi_sub_pL_lt : π - pL < pE := by have := pi_lt_pH; rw [pE_eq]; linarith

lemma pH_sub_pi_lt : pH - π < pE := by have := pL_lt_pi; rw [pE_eq]; linarith

lemma three_lt_pL : 3 < pL := by
  rw [lt_div_iff₀ SC_pos]; simp only [SC, PR, piLo]; norm_num

lemma pE_lt : pE < 1 / 2 ^ 64 := by
  rw [div_lt_div_iff₀ SC_pos (by positivity)]; simp only [SC, PR, piErr, piHi, piLo]; norm_num

lemma fx_mul_SC (n : ℤ) : fx n * SC = n := by
  rw [fx_eq]; field_simp

lemma cast_eq_fx_mul (n : ℤ) : (n : ℝ) = fx n * SC := (fx_mul_SC n).symm

lemma fx_add (a b : ℤ) : fx (a + b) = fx a + fx b := by simp only [fx_eq]; push_cast; ring
lemma fx_sub (a b : ℤ) : fx (a - b) = fx a - fx b := by simp only [fx_eq]; push_cast; ring
lemma fx_neg (a : ℤ) : fx (-a) = -fx a := by simp only [fx_eq]; push_cast; ring
lemma fx_mul_int (n a : ℤ) : fx (n * a) = n * fx a := by simp only [fx_eq]; push_cast; ring
lemma fx_le_iff {a b : ℤ} : fx a ≤ fx b ↔ a ≤ b := by
  simp only [fx_eq]; rw [div_le_div_iff_of_pos_right SC_pos]; exact_mod_cast Iff.rfl
lemma fx_lt_iff {a b : ℤ} : fx a < fx b ↔ a < b := by
  simp only [fx_eq]; rw [div_lt_div_iff_of_pos_right SC_pos]; exact_mod_cast Iff.rfl
lemma fx_zero : fx 0 = 0 := by simp [fx_eq]
lemma fx_pos_iff {a : ℤ} : 0 < fx a ↔ 0 < a := by rw [← fx_zero, fx_lt_iff]
lemma fx_nonneg_iff {a : ℤ} : 0 ≤ fx a ↔ 0 ≤ a := by rw [← fx_zero, fx_le_iff]

lemma fx_piLo : fx piLo = pL := rfl
lemma fx_piHi : fx piHi = pH := rfl
lemma fx_piErr : fx piErr = pE := rfl

/-! ## the function `G` -/

/-- `G(t) = 2ρ⟨u(t), w⟩ - d` for `w = (wx, wy)` -/
def Gf (ρ wx wy d t : ℝ) : ℝ := 2 * ρ * (wx * Real.cos t + wy * Real.sin t) - d

lemma Gf_add_int_mul_two_pi (ρ wx wy d t : ℝ) (n : ℤ) :
    Gf ρ wx wy d (t + n * (2 * π)) = Gf ρ wx wy d t := by
  simp only [Gf, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

lemma Gf_add_two_pi (ρ wx wy d t : ℝ) : Gf ρ wx wy d (t + 2 * π) = Gf ρ wx wy d t := by
  have := Gf_add_int_mul_two_pi ρ wx wy d t 1
  simpa using this

lemma Gf_add_pi (ρ wx wy d t : ℝ) : Gf ρ wx wy d (t + π) + Gf ρ wx wy d t = -2 * d := by
  simp only [Gf, Real.cos_add_pi, Real.sin_add_pi]; ring

/-- `sin(q - p) u(t) = sin(q - t) u(p) + sin(t - p) u(q)`, first coordinate -/
lemma slerp_cos (p q t : ℝ) :
    Real.sin (q - p) * Real.cos t = Real.sin (q - t) * Real.cos p + Real.sin (t - p) * Real.cos q := by
  rw [Real.sin_sub, Real.sin_sub, Real.sin_sub]; ring

/-- `sin(q - p) u(t) = sin(q - t) u(p) + sin(t - p) u(q)`, second coordinate -/
lemma slerp_sin (p q t : ℝ) :
    Real.sin (q - p) * Real.sin t = Real.sin (q - t) * Real.sin p + Real.sin (t - p) * Real.sin q := by
  rw [Real.sin_sub, Real.sin_sub, Real.sin_sub]; ring

lemma sin_add_le_of_nonneg {x y : ℝ} (hx0 : 0 ≤ x) (hxπ : x ≤ π) (hy0 : 0 ≤ y) (hyπ : y ≤ π) :
    Real.sin (x + y) ≤ Real.sin x + Real.sin y := by
  rw [Real.sin_add]
  have h1 := Real.sin_nonneg_of_nonneg_of_le_pi hx0 hxπ
  have h2 := Real.sin_nonneg_of_nonneg_of_le_pi hy0 hyπ
  have h3 := Real.cos_le_one x
  have h4 := Real.cos_le_one y
  nlinarith

/-- If `G > 0` at both ends of an interval of length `< π`, then `G > 0` on the interval. -/
lemma arc_pos {ρ wx wy d p q t : ℝ} (hd : 0 < d) (hpt : p ≤ t) (htq : t ≤ q) (hqp : q - p < π)
    (hp : 0 < Gf ρ wx wy d p) (hq : 0 < Gf ρ wx wy d q) : 0 < Gf ρ wx wy d t := by
  rcases eq_or_lt_of_le (le_trans hpt htq) with hpq | hpq
  · have : t = p := le_antisymm (hpq ▸ htq) hpt
    rw [this]; exact hp
  · have hX : d < 2 * ρ * (wx * Real.cos p + wy * Real.sin p) := by unfold Gf at hp; linarith
    have hY : d < 2 * ρ * (wx * Real.cos q + wy * Real.sin q) := by unfold Gf at hq; linarith
    have key : Real.sin (q - p) * (2 * ρ * (wx * Real.cos t + wy * Real.sin t))
        = Real.sin (q - t) * (2 * ρ * (wx * Real.cos p + wy * Real.sin p))
          + Real.sin (t - p) * (2 * ρ * (wx * Real.cos q + wy * Real.sin q)) := by
      linear_combination (2 * ρ * wx) * slerp_cos p q t + (2 * ρ * wy) * slerp_sin p q t
    have s1 : 0 ≤ Real.sin (q - t) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have s2 : 0 ≤ Real.sin (t - p) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have s3 : 0 < Real.sin (q - p) := Real.sin_pos_of_pos_of_lt_pi (by linarith) hqp
    have s4 : Real.sin (q - p) ≤ Real.sin (q - t) + Real.sin (t - p) := by
      have := sin_add_le_of_nonneg (x := q - t) (y := t - p) (by linarith) (by linarith) (by linarith)
        (by linarith)
      rwa [show q - t + (t - p) = q - p by ring] at this
    have hpos : 0 < Real.sin (q - t) * (2 * ρ * (wx * Real.cos p + wy * Real.sin p) - d)
        + Real.sin (t - p) * (2 * ρ * (wx * Real.cos q + wy * Real.sin q) - d) := by
      rcases eq_or_lt_of_le s1 with h1 | h1
      · have h2 : 0 < Real.sin (t - p) := by linarith
        rw [← h1]; simp only [zero_mul, zero_add]; exact mul_pos h2 (by linarith)
      · have := mul_pos h1 (sub_pos.mpr hX)
        have := mul_nonneg s2 (sub_pos.mpr hY).le
        linarith
    have hZ : Real.sin (q - p) * d < Real.sin (q - p) * (2 * ρ * (wx * Real.cos t + wy * Real.sin t)) := by
      rw [key]; nlinarith
    unfold Gf
    have := lt_of_mul_lt_mul_left hZ s3.le
    linarith

/-- If `G < 0` at `a` and `b` and `G(c) > 0` for some `c ∈ (a, b)`, every `t` with `G(t) > 0` is
congruent mod `2π` to a point of `(a, b)`. -/
lemma arc_in {ρ wx wy d a b c t : ℝ} (hd : 0 < d) (hac : a < c) (hcb : c < b)
    (ha : Gf ρ wx wy d a < 0) (hb : Gf ρ wx wy d b < 0) (hc : 0 < Gf ρ wx wy d c)
    (ht : 0 < Gf ρ wx wy d t) : ∃ n : ℤ, t + n * (2 * π) ∈ Ioo a b := by
  have h2π : 0 < 2 * π := Real.two_pi_pos
  set t' := toIcoMod h2π a t with ht'def
  have ht'eq : t' = t + ((-toIcoDiv h2π a t : ℤ) : ℝ) * (2 * π) := by
    rw [ht'def, ← self_sub_toIcoDiv_zsmul, zsmul_eq_mul]; push_cast; ring
  have hmem := toIcoMod_mem_Ico h2π a t
  rw [← ht'def] at hmem
  have hGt' : 0 < Gf ρ wx wy d t' := by rw [ht'eq, Gf_add_int_mul_two_pi]; exact ht
  refine ⟨-toIcoDiv h2π a t, ?_⟩
  rw [← ht'eq]
  constructor
  · rcases eq_or_lt_of_le hmem.1 with h | h
    · rw [← h] at hGt'; linarith
    · exact h
  · by_contra hge'
    have hge : b ≤ t' := not_lt.mp hge'
    rcases lt_trichotomy (t' - c) π with h1 | h1 | h1
    · have := arc_pos (t := b) hd hcb.le hge h1 hc hGt'
      linarith
    · have h2 := Gf_add_pi ρ wx wy d c
      rw [show c + π = t' by linarith] at h2
      linarith
    · have hc2 : 0 < Gf ρ wx wy d (c + 2 * π) := by rw [Gf_add_two_pi]; exact hc
      have ha2 : Gf ρ wx wy d (a + 2 * π) < 0 := by rw [Gf_add_two_pi]; exact ha
      have := arc_pos (p := t') (q := c + 2 * π) (t := a + 2 * π) hd (le_of_lt hmem.2) (by linarith)
        (by linarith) hGt' hc2
      linarith

/-! ## direction points -/

/-- the real value of a direction point (`2π` for the top) -/
def dval (p : DirPt) : ℝ := if p.top then 2 * π else fx p.t

/-- valid cos/sin enclosures at a direction point -/
def DirOK (p : DirPt) : Prop := ivMem (Real.cos (dval p)) p.c ∧ ivMem (Real.sin (dval p)) p.s

lemma dval_of_not_top {p : DirPt} (h : p.top = false) : dval p = fx p.t := by simp [dval, h]

/-! ## soundness of the arc certification -/

/-- scaled interval membership: `a.lo ≤ X ≤ a.hi` (so `ivMem x a ↔ ivMem' (x * SC) a`) -/
def ivMem' (X : ℝ) (a : Iv) : Prop := (a.lo : ℝ) ≤ X ∧ X ≤ a.hi

/-- the product enclosure used in `gh0` -/
def mI (w : ℤ) (a : Iv) : ℤ × ℤ := if 0 ≤ w then (w * a.lo, w * a.hi) else (w * a.hi, w * a.lo)

lemma mI_spec (w : ℤ) {a : Iv} {X : ℝ} (h1 : (a.lo : ℝ) ≤ X) (h2 : X ≤ a.hi) :
    ((mI w a).1 : ℝ) ≤ w * X ∧ w * X ≤ ((mI w a).2 : ℝ) := by
  unfold mI
  split_ifs with hw
  · have : (0 : ℝ) ≤ w := by exact_mod_cast hw
    simp only; push_cast; constructor <;> nlinarith
  · have : (w : ℝ) < 0 := by exact_mod_cast lt_of_not_ge hw
    simp only; push_cast; constructor <;> nlinarith

lemma gh0_eq (wx wy R : ℤ) (c s : Iv) : gh0 wx wy R c s =
    ((2 * R * ((mI wx c).1 + (mI wy s).1), 2 * R * ((mI wx c).2 + (mI wy s).2)),
     (2 * R * ((mI wx (Iv.neg s)).1 + (mI wy c).1), 2 * R * ((mI wx (Iv.neg s)).2 + (mI wy c).2))) := rfl

/-- `gh0` encloses `2R⟨u, w⟩` and `2R⟨u', w⟩` (all scaled), for `R ≥ 0`. -/
lemma gh0_spec (wx wy R : ℤ) (hR : 0 ≤ R) {c s : Iv} {X Y : ℝ} (hX : ivMem' X c) (hY : ivMem' Y s) :
    ((gh0 wx wy R c s).1.1 : ℝ) ≤ 2 * R * (wx * X + wy * Y) ∧
    2 * R * (wx * X + wy * Y) ≤ ((gh0 wx wy R c s).1.2 : ℝ) ∧
    ((gh0 wx wy R c s).2.1 : ℝ) ≤ 2 * R * (wx * (-Y) + wy * X) ∧
    2 * R * (wx * (-Y) + wy * X) ≤ ((gh0 wx wy R c s).2.2 : ℝ) := by
  rw [gh0_eq]
  have hR' : (0 : ℝ) ≤ R := by exact_mod_cast hR
  obtain ⟨a1, a2⟩ := mI_spec wx hX.1 hX.2
  obtain ⟨b1, b2⟩ := mI_spec wy hY.1 hY.2
  have hnY1 : ((Iv.neg s).lo : ℝ) ≤ -Y := by simp only [Iv.neg]; push_cast; linarith [hY.2]
  have hnY2 : -Y ≤ ((Iv.neg s).hi : ℝ) := by simp only [Iv.neg]; push_cast; linarith [hY.1]
  obtain ⟨c1, c2⟩ := mI_spec wx hnY1 hnY2
  obtain ⟨d1, d2⟩ := mI_spec wy hX.1 hX.2
  simp only; push_cast
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- the lower part of `gShift`: `cos ε · G0` with `cos ε ∈ [cl, 1]` (scaled by `SC`), `cos ε ≥ 0` -/
lemma gShift_a {G0 : ℤ × ℤ} {g C : ℝ} (cl : ℤ) (hg1 : (G0.1 : ℝ) ≤ g) (hg2 : g ≤ G0.2)
    (hC0 : 0 ≤ C) (hC1 : C ≤ SC) (hC2 : (cl : ℝ) ≤ C) :
    (((if 0 ≤ G0.1 then G0.1 * cl else G0.1 * ONE : ℤ)) : ℝ) ≤ C * g ∧
    C * g ≤ (((if 0 ≤ G0.2 then G0.2 * ONE else G0.2 * cl : ℤ)) : ℝ) := by
  constructor
  · split_ifs with h
    · have : (0 : ℝ) ≤ G0.1 := by exact_mod_cast h
      push_cast; nlinarith
    · have : (G0.1 : ℝ) < 0 := by exact_mod_cast lt_of_not_ge h
      push_cast; rw [ONE_cast]; nlinarith
  · split_ifs with h
    · have : (0 : ℝ) ≤ G0.2 := by exact_mod_cast h
      push_cast; rw [ONE_cast]; nlinarith
    · have : (G0.2 : ℝ) < 0 := by exact_mod_cast lt_of_not_ge h
      push_cast; nlinarith

/-- the second part of `gShift`: `sin ε · H0` with `sin ε ∈ [sl, e]` (scaled), `sin ε ≥ 0` -/
lemma gShift_h {H0 : ℤ × ℤ} {h S : ℝ} (sl e : ℤ) (hh1 : (H0.1 : ℝ) ≤ h) (hh2 : h ≤ H0.2)
    (hS0 : 0 ≤ S) (hS1 : S ≤ e) (hS2 : (sl : ℝ) ≤ S) :
    (((if 0 ≤ H0.1 then H0.1 * sl else H0.1 * e : ℤ)) : ℝ) ≤ S * h ∧
    S * h ≤ (((if 0 ≤ H0.2 then H0.2 * e else H0.2 * sl : ℤ)) : ℝ) := by
  constructor
  · split_ifs with hc
    · have : (0 : ℝ) ≤ H0.1 := by exact_mod_cast hc
      push_cast; nlinarith
    · have : (H0.1 : ℝ) < 0 := by exact_mod_cast lt_of_not_ge hc
      push_cast; nlinarith
  · split_ifs with hc
    · have : (0 : ℝ) ≤ H0.2 := by exact_mod_cast hc
      push_cast; nlinarith
    · have : (H0.2 : ℝ) < 0 := by exact_mod_cast lt_of_not_ge hc
      push_cast; nlinarith

lemma gShift_spec {G0 H0 : ℤ × ℤ} {g h C S : ℝ} (d2 e ce se : ℤ) (plus : Bool)
    (hg1 : (G0.1 : ℝ) ≤ g) (hg2 : g ≤ G0.2) (hh1 : (H0.1 : ℝ) ≤ h) (hh2 : h ≤ H0.2)
    (hC0 : 0 ≤ C) (hC1 : C ≤ SC) (hC2 : ((ONE - ce : ℤ) : ℝ) ≤ C)
    (hS0 : 0 ≤ S) (hS1 : S ≤ e) (hS2 : ((e - se : ℤ) : ℝ) ≤ S) :
    ((gShift G0 H0 d2 e ce se plus).1 : ℝ) ≤ C * g + (if plus then S * h else -(S * h)) - d2 * SC * SC ∧
    C * g + (if plus then S * h else -(S * h)) - d2 * SC * SC ≤ ((gShift G0 H0 d2 e ce se plus).2 : ℝ) := by
  obtain ⟨a1, a2⟩ := gShift_a (ONE - ce) hg1 hg2 hC0 hC1 hC2
  obtain ⟨b1, b2⟩ := gShift_h (e - se) e hh1 hh2 hS0 hS1 hS2
  cases plus
  · simp only [gShift, Bool.false_eq_true, ite_false]
    push_cast at a1 a2 b1 b2 ⊢
    rw [ONE_cast] at *
    constructor <;> linarith
  · simp only [gShift, ite_true]
    push_cast at a1 a2 b1 b2 ⊢
    rw [ONE_cast] at *
    constructor <;> linarith

/-! ## the trigonometric bounds at `ε` -/

lemma eps_trig {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) :
    0 ≤ Real.cos ε ∧ Real.cos ε ≤ 1 ∧ 1 - ε ^ 2 / 2 ≤ Real.cos ε ∧
    0 ≤ Real.sin ε ∧ Real.sin ε ≤ ε ∧ ε - ε ^ 3 / 4 ≤ Real.sin ε := by
  refine ⟨?_, Real.cos_le_one ε, Real.one_sub_sq_div_two_le_cos, ?_, Real.sin_le h0.le, ?_⟩
  · apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le <;> linarith [Real.pi_gt_three]
  · exact Real.sin_nonneg_of_nonneg_of_le_pi h0.le (by linarith [Real.pi_gt_three])
  · have := Real.sin_gt_sub_cube h0; nlinarith [pow_pos h0 3]

lemma two_pow_PR_succ : (2 : ℝ) ^ (PR + 1) = 2 * SC := by rw [pow_succ]; ring
lemma two_pow_two_PR_add_two : (2 : ℝ) ^ (2 * PR + 2) = 4 * SC ^ 2 := by
  rw [pow_add, pow_mul']; norm_num; ring

/-- `ONE - ce ≤ (1 - ε²/2) · SC` -/
lemma ce_bound (e : ℤ) : ((ONE - (shrU (e * e) (PR + 1) + 1) : ℤ) : ℝ) ≤ (1 - fx e ^ 2 / 2) * SC := by
  have h := le_shrU (e * e) (PR + 1)
  rw [two_pow_PR_succ] at h
  push_cast at h ⊢
  rw [ONE_cast, fx_eq]
  have hS := SC_pos
  have e1 : (1 - ((e : ℝ) / SC) ^ 2 / 2) * SC = SC - (e : ℝ) * e / (2 * SC) := by field_simp
  rw [e1]; linarith

/-- `e - se ≤ (ε - ε³/4) · SC` -/
lemma se_bound (e : ℤ) :
    ((e - (shrU (e * e * e) (2 * PR + 2) + 1) : ℤ) : ℝ) ≤ (fx e - fx e ^ 3 / 4) * SC := by
  have h := le_shrU (e * e * e) (2 * PR + 2)
  rw [two_pow_two_PR_add_two] at h
  push_cast at h ⊢
  rw [fx_eq]
  have hS := SC_pos
  have e1 : ((e : ℝ) / SC - ((e : ℝ) / SC) ^ 3 / 4) * SC = e - (e : ℝ) * e * e / (4 * SC ^ 2) := by
    field_simp
  rw [e1]; linarith

/-! ## soundness of `certArcWith` -/

/-- what a successful `certArcWith` gives, in integers -/
lemma certArcWith_spec {wx wy d2 R θL θH : ℤ} {cL sL cH sH : Iv} {e : ℤ} {ar : Arc}
    (h : certArcWith wx wy d2 R θL θH cL sL cH sH e = some ar) :
    ar = ⟨⟨θL, false, cL, sL⟩, ⟨θH, false, cH, sH⟩, 4 * e⟩ ∧ θL + e ≤ θH - e ∧ (θH + e) - (θL - e) < piLo ∧
    (gShift (gh0 wx wy R cL sL).1 (gh0 wx wy R cL sL).2 d2 e (shrU (e * e) (PR + 1) + 1)
        (shrU (e * e * e) (2 * PR + 2) + 1) false).2 < 0 ∧
    0 < (gShift (gh0 wx wy R cL sL).1 (gh0 wx wy R cL sL).2 d2 e (shrU (e * e) (PR + 1) + 1)
        (shrU (e * e * e) (2 * PR + 2) + 1) true).1 ∧
    0 < (gShift (gh0 wx wy R cH sH).1 (gh0 wx wy R cH sH).2 d2 e (shrU (e * e) (PR + 1) + 1)
        (shrU (e * e * e) (2 * PR + 2) + 1) false).1 ∧
    (gShift (gh0 wx wy R cH sH).1 (gh0 wx wy R cH sH).2 d2 e (shrU (e * e) (PR + 1) + 1)
        (shrU (e * e * e) (2 * PR + 2) + 1) true).2 < 0 := by
  unfold certArcWith at h
  split_ifs at h with h1
  rcases hL : gh0 wx wy R cL sL with ⟨gL0, hL0⟩
  rcases hH : gh0 wx wy R cH sH with ⟨gH0, hH0⟩
  rw [hL, hH] at h
  dsimp only at h
  split_ifs at h with h2
  simp only [Option.some.injEq] at h
  exact ⟨h.symm, h1.1, h1.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2⟩

/-- `G(θ ± ε) · SC⁴` in terms of the scaled quantities of `gh0` and `gShift` -/
lemma G_shift_identity (R wx wy d2 : ℤ) (hd2 : d2 = wx * wx + wy * wy) (θ ε : ℝ) (plus : Bool) :
    Gf (fx R) (fx wx) (fx wy) (fx wx ^ 2 + fx wy ^ 2) (if plus then θ + ε else θ - ε) * SC ^ 4 =
      (Real.cos ε * SC) * (2 * R * (wx * (Real.cos θ * SC) + wy * (Real.sin θ * SC)))
      + (if plus then (Real.sin ε * SC) * (2 * R * (wx * (-(Real.sin θ * SC)) + wy * (Real.cos θ * SC)))
         else -((Real.sin ε * SC) * (2 * R * (wx * (-(Real.sin θ * SC)) + wy * (Real.cos θ * SC)))))
      - d2 * SC * SC := by
  have hS := SC_pos.ne'
  subst hd2
  cases plus
  · simp only [Gf, Bool.false_eq_true, ite_false, Real.cos_sub, Real.sin_sub, fx_eq]
    push_cast; field_simp; ring
  · simp only [Gf, ite_true, Real.cos_add, Real.sin_add, fx_eq]
    push_cast; field_simp; ring

/-- the real meaning of one `gShift` test -/
lemma gShift_G {wx wy d2 R θ e : ℤ} {c s : Iv} (hR : 0 ≤ R) (hd2 : d2 = wx * wx + wy * wy)
    (he0 : 0 < e) (he1 : e ≤ ONE) (hc : ivMem (Real.cos (fx θ)) c) (hs : ivMem (Real.sin (fx θ)) s)
    (plus : Bool) :
    ((gShift (gh0 wx wy R c s).1 (gh0 wx wy R c s).2 d2 e (shrU (e * e) (PR + 1) + 1)
        (shrU (e * e * e) (2 * PR + 2) + 1) plus).1 : ℝ)
      ≤ Gf (fx R) (fx wx) (fx wy) (fx wx ^ 2 + fx wy ^ 2)
          (if plus then fx θ + fx e else fx θ - fx e) * SC ^ 4 ∧
    Gf (fx R) (fx wx) (fx wy) (fx wx ^ 2 + fx wy ^ 2) (if plus then fx θ + fx e else fx θ - fx e) * SC ^ 4
      ≤ ((gShift (gh0 wx wy R c s).1 (gh0 wx wy R c s).2 d2 e (shrU (e * e) (PR + 1) + 1)
        (shrU (e * e * e) (2 * PR + 2) + 1) plus).2 : ℝ) := by
  have hS := SC_pos
  have hε0 : 0 < fx e := fx_pos_iff.mpr he0
  have hε1 : fx e ≤ 1 := by
    have : fx e ≤ fx ONE := fx_le_iff.mpr he1
    rwa [show fx ONE = 1 by rw [fx_eq, ONE_cast]; exact div_self hS.ne'] at this
  obtain ⟨c0, c1, c2, s0, s1, s2⟩ := eps_trig hε0 hε1
  have hX : ivMem' (Real.cos (fx θ) * SC) c := hc
  have hY : ivMem' (Real.sin (fx θ) * SC) s := hs
  obtain ⟨g1, g2, h1, h2⟩ := gh0_spec wx wy R hR hX hY
  have hC0 : 0 ≤ Real.cos (fx e) * SC := mul_nonneg c0 hS.le
  have hC1 : Real.cos (fx e) * SC ≤ SC := by nlinarith
  have hC2 : ((ONE - (shrU (e * e) (PR + 1) + 1) : ℤ) : ℝ) ≤ Real.cos (fx e) * SC :=
    le_trans (ce_bound e) (by nlinarith)
  have hS0 : 0 ≤ Real.sin (fx e) * SC := mul_nonneg s0 hS.le
  have hS1 : Real.sin (fx e) * SC ≤ e := by rw [cast_eq_fx_mul e]; nlinarith
  have hS2 : ((e - (shrU (e * e * e) (2 * PR + 2) + 1) : ℤ) : ℝ) ≤ Real.sin (fx e) * SC :=
    le_trans (se_bound e) (by nlinarith)
  have key := gShift_spec d2 e (shrU (e * e) (PR + 1) + 1) (shrU (e * e * e) (2 * PR + 2) + 1) plus
    g1 g2 h1 h2 hC0 hC1 hC2 hS0 hS1 hS2
  rw [G_shift_identity R wx wy d2 hd2 (fx θ) (fx e) plus]
  exact key

/-- A certified arc: the data that the measure argument uses. -/
def ArcCert (G : ℝ → ℝ) (ar : Arc) : Prop :=
  ∃ e : ℤ, 4 * piErr ≤ e ∧ e ≤ 2 ^ (PR - 16) ∧ ar.slack = 4 * e ∧
    ar.s.top = false ∧ ar.e.top = false ∧
    -(2 * piLo) ≤ ar.s.t ∧ ar.s.t ≤ piLo ∧ ar.s.t + e ≤ ar.e.t - e ∧ (ar.e.t + e) - (ar.s.t - e) < piLo ∧
    DirOK ar.s ∧ DirOK ar.e ∧
    G (fx ar.s.t - fx e) < 0 ∧ 0 < G (fx ar.s.t + fx e) ∧ 0 < G (fx ar.e.t - fx e) ∧ G (fx ar.e.t + fx e) < 0

lemma foldl_first (f : ℤ → Option Arc) : ∀ (l : List ℤ) (init : Option Arc) (ar : Arc),
    l.foldl (fun acc e => match acc with | some a => some a | none => f e) init = some ar →
    init = some ar ∨ ∃ e ∈ l, f e = some ar
  | [], init, ar, h => Or.inl h
  | e :: l, init, ar, h => by
    simp only [List.foldl_cons] at h
    rcases foldl_first f l _ ar h with h' | ⟨e', he', h'⟩
    · cases init with
      | some a => left; simpa using h'
      | none => right; exact ⟨e, by simp, by simpa using h'⟩
    · right; exact ⟨e', by simp [he'], h'⟩

lemma epsList_bounds : ∀ e ∈ epsList, 4 * piErr ≤ e ∧ e ≤ 2 ^ (PR - 16) := by
  intro e he
  simp only [epsList, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> constructor <;> norm_num [piErr, piHi, piLo, PR]

/-- Soundness of `certArc`. -/
theorem certArc_spec (cs : ℤ → Iv × Iv) (hcs : CosSinSound cs) {wx wy d2 R : ℤ} (hR : 0 ≤ R)
    (hd2 : d2 = wx * wx + wy * wy) {cand : CandFn} {ar : Arc} (h : certArc cs wx wy d2 R cand = some ar) :
    ArcCert (Gf (fx R) (fx wx) (fx wy) (fx wx ^ 2 + fx wy ^ 2)) ar := by
  unfold certArc at h
  rcases hc : cand wx wy d2 R with ⟨θL, θH⟩
  rw [hc] at h
  dsimp only at h
  split_ifs at h with hr
  rcases hL : cs θL with ⟨cL, sL⟩
  rcases hH : cs θH with ⟨cH, sH⟩
  rw [hL, hH] at h
  dsimp only at h
  rcases foldl_first _ epsList none ar h with h' | ⟨e, he, h'⟩
  · exact absurd h' (by simp)
  obtain ⟨he1, he2⟩ := epsList_bounds e he
  have hcsL := hcs θL hr.1
  have hcsH := hcs θH hr.2.1
  rw [hL] at hcsL
  rw [hH] at hcsH
  have he0 : 0 < e := lt_of_lt_of_le (by norm_num [piErr, piHi, piLo]) he1
  have heONE : e ≤ ONE := le_trans he2 (by norm_num [ONE, PR])
  obtain ⟨har, h1, h2, g1, g2, g3, g4⟩ := certArcWith_spec h'
  have k1 := (gShift_G hR hd2 he0 heONE hcsL.1 hcsL.2 false).2
  have k2 := (gShift_G hR hd2 he0 heONE hcsL.1 hcsL.2 true).1
  have k3 := (gShift_G hR hd2 he0 heONE hcsH.1 hcsH.2 false).1
  have k4 := (gShift_G hR hd2 he0 heONE hcsH.1 hcsH.2 true).2
  simp only [Bool.false_eq_true, ite_false, ite_true] at k1 k2 k3 k4
  have hS4 : (0 : ℝ) < SC ^ 4 := by have := SC_pos; positivity
  subst har
  refine ⟨e, he1, he2, rfl, rfl, rfl, hr.2.2.1, hr.2.2.2, h1, h2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by simpa [dval] using hcsL.1, by simpa [dval] using hcsL.2⟩
  · exact ⟨by simpa [dval] using hcsH.1, by simpa [dval] using hcsH.2⟩
  · have g1r := (Int.cast_lt.mpr g1 : ((_ : ℤ) : ℝ) < ((0 : ℤ) : ℝ))
    rw [Int.cast_zero] at g1r
    nlinarith
  · have g2r := (Int.cast_lt.mpr g2 : ((0 : ℤ) : ℝ) < ((_ : ℤ) : ℝ))
    rw [Int.cast_zero] at g2r
    nlinarith
  · have g3r := (Int.cast_lt.mpr g3 : ((0 : ℤ) : ℝ) < ((_ : ℤ) : ℝ))
    rw [Int.cast_zero] at g3r
    nlinarith
  · have g4r := (Int.cast_lt.mpr g4 : ((_ : ℤ) : ℝ) < ((0 : ℤ) : ℝ))
    rw [Int.cast_zero] at g4r
    nlinarith

end US

end

end BHH
