/-
Interval helpers for the table soundness T1–T4 (`W2Cert/Table.lean`): enclosures of the radii and of `dθ`,
`cos`/`sin` of angle intervals (`cosIvG`, `sinIvG`, `cosIvDec`, by monotone pieces of `cos` and `sin`), and the
closed form of `A_1` (`a1Pt`, `a1Iv`).
-/
import W2.FixSound
import W2.Unroll
import W2Cert.Table

open Set Real BHH.Cert

noncomputable section

namespace BHH.W2.TabB

open BHH BHH.W2 W2C

/-! ## basics -/

lemma ivMem_iff {x : ℝ} {a : Iv} : ivMem x a ↔ fx a.lo ≤ x ∧ x ≤ fx a.hi :=
  ⟨fun h => ⟨ivMem_lo_le h, ivMem_hi_le h⟩, fun h => ivMem_of_fx h.1 h.2⟩

lemma two_pow_PR : ((ONE : ℤ) : ℝ) = (2 : ℝ) ^ PR := ONE_cast

lemma fx_ONE : fx ONE = 1 := by
  unfold fx; rw [two_pow_PR]; exact div_self (by positivity)

lemma fx_negONE : fx (-ONE) = -1 := by rw [fx_neg, fx_ONE]

lemma fx_min (A B : ℤ) : fx (min A B) = min (fx A) (fx B) := by
  rcases le_total A B with h | h
  · rw [min_eq_left h, min_eq_left (fx_le_iff.mpr h)]
  · rw [min_eq_right h, min_eq_right (fx_le_iff.mpr h)]

lemma fx_max (A B : ℤ) : fx (max A B) = max (fx A) (fx B) := by
  rcases le_total A B with h | h
  · rw [max_eq_right h, max_eq_right (fx_le_iff.mpr h)]
  · rw [max_eq_left h, max_eq_left (fx_le_iff.mpr h)]

lemma fx_two_mul (A : ℤ) : fx (2 * A) = 2 * fx A := by unfold fx; push_cast; ring

lemma natAbs_le_seven {θ : ℤ} (h0 : -(2 * piHi) ≤ θ) (h1 : θ ≤ 2 * piHi) : θ.natAbs ≤ 7 * ONE.toNat := by
  have h7 : (2 * piHi).natAbs ≤ 7 * ONE.toNat := by unfold piHi ONE; norm_num
  have hp : 0 ≤ piHi := by unfold piHi; norm_num
  omega

/-- an angle strictly inside `(-2π, 2π)` is a valid argument of `cosSin` -/
lemma natAbs_of_two_pi {θ : ℤ} (h0 : -(2 * π) < fx θ) (h1 : fx θ < 2 * π) : θ.natAbs ≤ 7 * ONE.toNat := by
  have hp := le_piHi
  apply natAbs_le_seven
  · have : fx (-(2 * piHi)) < fx θ := by rw [fx_neg, fx_two_mul]; linarith
    exact (fx_lt_iff.mp this).le
  · have : fx θ < fx (2 * piHi) := by rw [fx_two_mul]; linarith
    exact (fx_lt_iff.mp this).le

/-! ## radii and `dθ` -/

lemma mem_ratIv (a : ℤ) {b : ℕ} (hb : 0 < b) : ivMem ((a : ℝ) / b) (ratIv a b) := by
  have hb' : (0 : ℤ) < (b : ℤ) := by exact_mod_cast hb
  unfold ratIv ivMem
  simp only
  have e : ((a * ONE : ℤ) : ℝ) / ((b : ℤ) : ℝ) = (a : ℝ) / b * 2 ^ PR := by
    push_cast; rw [two_pow_PR]; ring
  constructor
  · rw [← e]; exact divD_le _ _ hb'
  · rw [← e]; exact le_divU _ _ hb'

lemma mem_radIv (g : W2C.Grid) (h1 : 0 < g.N1) (h2 : 0 < g.N2) (j : ℕ) :
    ivMem ((gR g).rad j) (radIv g j) := by
  unfold radIv GridR.rad gR
  simp only
  split_ifs with hj
  · have := mem_ratIv (j : ℤ) h1
    push_cast at this
    exact this
  · have := Iv.mem_add (Iv.mem_int 1) (mem_ratIv ((j : ℤ) - g.N1) h2)
    have e : (((j : ℤ) - g.N1 : ℤ) : ℝ) = ((j - g.N1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [Int.cast_one, e] at this
    exact this

lemma mem_dthIv (g : W2C.Grid) (hNT : 0 < g.NT) : ivMem (π / g.NT) (dthIv g) := by
  have hb : (0 : ℤ) < (g.NT : ℤ) := by exact_mod_cast hNT
  have hNTr : (0 : ℝ) < g.NT := by exact_mod_cast hNT
  have p1 := piLo_le
  have p2 := le_piHi
  unfold fx at p1 p2
  have hS : (0 : ℝ) < 2 ^ PR := by positivity
  have q1 : (piLo : ℝ) ≤ π * 2 ^ PR := by rwa [div_le_iff₀ hS] at p1
  have q2 : π * 2 ^ PR ≤ (piHi : ℝ) := by rwa [le_div_iff₀ hS] at p2
  have e1 : (piLo : ℝ) / ((g.NT : ℤ) : ℝ) ≤ π / g.NT * 2 ^ PR := by
    rw [Int.cast_natCast, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hNTr]
    exact q1
  have e2 : π / g.NT * 2 ^ PR ≤ (piHi : ℝ) / ((g.NT : ℤ) : ℝ) := by
    rw [Int.cast_natCast, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hNTr]
    exact q2
  unfold dthIv ivMem
  simp only
  exact ⟨(divD_le _ _ hb).trans e1, e2.trans (le_divU _ _ hb)⟩

/-! ## monotone pieces of `cos` and `sin` -/

lemma min_le_of_peak {f : ℝ → ℝ} {p q r lo hi x : ℝ} (hm : MonotoneOn f (Icc p q))
    (ha : AntitoneOn f (Icc q r)) (hp : p ≤ lo) (hlx : lo ≤ x) (hxh : x ≤ hi) (hr : hi ≤ r) :
    min (f lo) (f hi) ≤ f x := by
  rcases le_total x q with hxq | hxq
  · exact (min_le_left _ _).trans (hm ⟨hp, hlx.trans hxq⟩ ⟨hp.trans hlx, hxq⟩ hlx)
  · exact (min_le_right _ _).trans (ha ⟨hxq, hxh.trans hr⟩ ⟨hxq.trans hxh, hr⟩ hxh)

lemma le_max_of_valley {f : ℝ → ℝ} {p q r lo hi x : ℝ} (ha : AntitoneOn f (Icc p q))
    (hm : MonotoneOn f (Icc q r)) (hp : p ≤ lo) (hlx : lo ≤ x) (hxh : x ≤ hi) (hr : hi ≤ r) :
    f x ≤ max (f lo) (f hi) := by
  rcases le_total x q with hxq | hxq
  · exact (ha ⟨hp, hlx.trans hxq⟩ ⟨hp.trans hlx, hxq⟩ hlx).trans (le_max_left _ _)
  · exact (hm ⟨hxq, hxh.trans hr⟩ ⟨hxq.trans hxh, hr⟩ hxh).trans (le_max_right _ _)

lemma cos_anti_0pi : AntitoneOn cos (Icc 0 π) := Real.strictAntiOn_cos.antitoneOn

lemma cos_mono_negpi0 : MonotoneOn cos (Icc (-π) 0) := by
  intro a ha b hb hab
  rw [← Real.cos_neg a, ← Real.cos_neg b]
  exact cos_anti_0pi ⟨by linarith [hb.2], by linarith [hb.1]⟩ ⟨by linarith [ha.2], by linarith [ha.1]⟩
    (by linarith)

lemma cos_mono_pi2pi : MonotoneOn cos (Icc π (2 * π)) := by
  intro a ha b hb hab
  rw [← Real.cos_sub_two_pi a, ← Real.cos_sub_two_pi b]
  exact cos_mono_negpi0 ⟨by linarith [ha.1], by linarith [ha.2]⟩ ⟨by linarith [hb.1], by linarith [hb.2]⟩
    (by linarith)

lemma cos_anti_neg2pi : AntitoneOn cos (Icc (-(2 * π)) (-π)) := by
  intro a ha b hb hab
  rw [← Real.cos_add_two_pi a, ← Real.cos_add_two_pi b]
  exact cos_anti_0pi ⟨by linarith [ha.1], by linarith [ha.2]⟩ ⟨by linarith [hb.1], by linarith [hb.2]⟩
    (by linarith)

lemma sin_mono_half : MonotoneOn sin (Icc (-(π / 2)) (π / 2)) := Real.strictMonoOn_sin.monotoneOn

lemma sin_anti_half : AntitoneOn sin (Icc (π / 2) (3 * π / 2)) := by
  intro a ha b hb hab
  rw [← Real.sin_pi_sub a, ← Real.sin_pi_sub b]
  exact sin_mono_half ⟨by linarith [hb.2], by linarith [hb.1]⟩ ⟨by linarith [ha.2], by linarith [ha.1]⟩
    (by linarith)

lemma sin_eq_neg_pi_sub (t : ℝ) : sin t = sin (-π - t) := by
  rw [show -π - t = -(t + π) by ring, Real.sin_neg, Real.sin_add_pi, neg_neg]

lemma sin_anti_neghalf : AntitoneOn sin (Icc (-(3 * π / 2)) (-(π / 2))) := by
  intro a ha b hb hab
  rw [sin_eq_neg_pi_sub a, sin_eq_neg_pi_sub b]
  exact sin_mono_half ⟨by linarith [hb.2], by linarith [hb.1]⟩ ⟨by linarith [ha.2], by linarith [ha.1]⟩
    (by linarith)

/-! ## `cos` and `sin` of angle intervals -/

lemma cos_pt_mem {t : ℤ} (h0 : -(2 * π) < fx t) (h1 : fx t < 2 * π) : ivMem (cos (fx t)) (cosSin t).1 :=
  (cosSin_sound t (natAbs_of_two_pi h0 h1)).1

lemma sin_pt_mem {t : ℤ} (h0 : -(2 * π) < fx t) (h1 : fx t < 2 * π) : ivMem (sin (fx t)) (cosSin t).2 :=
  (cosSin_sound t (natAbs_of_two_pi h0 h1)).2

/-- `cosIvG` encloses `cos` on an angle interval inside `(-2π, 2π)` -/
theorem mem_cosIvG {x : ℝ} {a : Iv} (hx : ivMem x a) (hlo : -(2 * π) < fx a.lo) (hhi : fx a.hi < 2 * π) :
    ivMem (cos x) (cosIvG a) := by
  obtain ⟨hx1, hx2⟩ := ivMem_iff.mp hx
  have hc1 := cos_pt_mem hlo (by linarith)
  have hc2 := cos_pt_mem (t := a.hi) (by linarith) hhi
  have pl := piLo_le
  have ph := le_piHi
  unfold cosIvG
  dsimp only
  apply ivMem_of_fx
  · split_ifs with h
    · rw [fx_negONE]; exact neg_one_le_cos x
    · rw [not_or, not_and_or, not_and_or, not_le, not_le, not_le, not_le] at h
      obtain ⟨hA, hB⟩ := h
      have key : min (cos (fx a.lo)) (cos (fx a.hi)) ≤ cos x := by
        rcases hA with hA | hA
        · -- the interval is in `(π, 2π)`
          have : π < fx a.lo := lt_of_le_of_lt ph (fx_lt_iff.mpr hA)
          exact (min_le_left _ _).trans
            (cos_mono_pi2pi ⟨this.le, by linarith⟩ ⟨by linarith, by linarith⟩ hx1)
        · have hA' : fx a.hi < π := lt_of_lt_of_le (fx_lt_iff.mpr hA) pl
          rcases hB with hB | hB
          · have : -π < fx a.lo := by
              have := fx_lt_iff.mpr hB; rw [fx_neg] at this; linarith
            exact min_le_of_peak cos_mono_negpi0 cos_anti_0pi this.le hx1 hx2 hA'.le
          · -- the interval is in `(-2π, -π)`
            have : fx a.hi < -π := by
              have := fx_lt_iff.mpr hB; rw [fx_neg] at this; linarith
            exact (min_le_right _ _).trans
              (cos_anti_neg2pi ⟨by linarith, by linarith⟩ ⟨by linarith, this.le⟩ hx2)
      rw [fx_min]
      exact (min_le_min (ivMem_lo_le hc1) (ivMem_lo_le hc2)).trans key
  · split_ifs with h
    · rw [fx_ONE]; exact cos_le_one x
    · rw [not_and_or, not_le, not_le] at h
      have key : cos x ≤ max (cos (fx a.lo)) (cos (fx a.hi)) := by
        rcases h with h | h
        · have : 0 < fx a.lo := by have := fx_lt_iff.mpr h; unfold fx at this ⊢; simpa using this
          exact le_max_of_valley cos_anti_0pi cos_mono_pi2pi this.le hx1 hx2 hhi.le
        · have : fx a.hi < 0 := by have := fx_lt_iff.mpr h; unfold fx at this ⊢; simpa using this
          exact le_max_of_valley cos_anti_neg2pi cos_mono_negpi0 hlo.le hx1 hx2 this.le
      rw [fx_max]
      exact key.trans (max_le_max (ivMem_hi_le hc1) (ivMem_hi_le hc2))

/-- `sinIvG` encloses `sin` on an angle interval inside `(-3π/2, 3π/2)` -/
theorem mem_sinIvG {x : ℝ} {a : Iv} (hx : ivMem x a) (hlo : -(3 * π / 2) < fx a.lo)
    (hhi : fx a.hi < 3 * π / 2) : ivMem (sin x) (sinIvG a) := by
  obtain ⟨hx1, hx2⟩ := ivMem_iff.mp hx
  have hpi := pi_pos
  have hs1 := sin_pt_mem (t := a.lo) (by linarith) (by linarith)
  have hs2 := sin_pt_mem (t := a.hi) (by linarith) (by linarith)
  have hl := halfPiLo_le
  have hh := le_halfPiHi
  unfold sinIvG
  dsimp only
  apply ivMem_of_fx
  · split_ifs with h
    · rw [fx_negONE]; exact neg_one_le_sin x
    · rw [not_and_or, not_le, not_le] at h
      have key : min (sin (fx a.lo)) (sin (fx a.hi)) ≤ sin x := by
        rcases h with h | h
        · have : -(π / 2) < fx a.lo := by
            have := fx_lt_iff.mpr h; rw [fx_neg] at this; linarith
          exact min_le_of_peak sin_mono_half sin_anti_half this.le hx1 hx2 hhi.le
        · have : fx a.hi < -(π / 2) := by
            have := fx_lt_iff.mpr h; rw [fx_neg] at this; linarith
          exact (min_le_right _ _).trans
            (sin_anti_neghalf ⟨by linarith, by linarith⟩ ⟨by linarith, this.le⟩ hx2)
      rw [fx_min]
      exact (min_le_min (ivMem_lo_le hs1) (ivMem_lo_le hs2)).trans key
  · split_ifs with h
    · rw [fx_ONE]; exact sin_le_one x
    · rw [not_and_or, not_le, not_le] at h
      have key : sin x ≤ max (sin (fx a.lo)) (sin (fx a.hi)) := by
        rcases h with h | h
        · have : π / 2 < fx a.lo := lt_of_le_of_lt hh (fx_lt_iff.mpr h)
          exact (sin_anti_half ⟨this.le, by linarith⟩ ⟨by linarith, by linarith⟩ hx1).trans (le_max_left _ _)
        · have : fx a.hi < π / 2 := lt_of_lt_of_le (fx_lt_iff.mpr h) hl
          exact le_max_of_valley sin_anti_neghalf sin_mono_half hlo.le hx1 hx2 this.le
      rw [fx_max]
      exact key.trans (max_le_max (ivMem_hi_le hs1) (ivMem_hi_le hs2))

/-- `cosIvDec` encloses `cos` on an angle interval inside `[0, π]` -/
theorem mem_cosIvDec {x : ℝ} {a : Iv} (hx : ivMem x a) (hlo : 0 ≤ fx a.lo) (hhi : fx a.hi ≤ π) :
    ivMem (cos x) (cosIvDec a) := by
  obtain ⟨hx1, hx2⟩ := ivMem_iff.mp hx
  have hpi := pi_pos
  have hc1 := cos_pt_mem (t := a.lo) (by linarith) (by linarith)
  have hc2 := cos_pt_mem (t := a.hi) (by linarith) (by linarith)
  unfold cosIvDec
  apply ivMem_of_fx
  · exact (ivMem_lo_le hc2).trans (cos_anti_0pi ⟨by linarith, by linarith⟩ ⟨by linarith, hhi⟩ hx2)
  · exact (cos_anti_0pi ⟨hlo, by linarith⟩ ⟨by linarith, by linarith⟩ hx1).trans (ivMem_hi_le hc1)

/-! ## the closed form of `A_1` -/

theorem a1Pt_spec (p : ℤ) : ivMem (A1c (fx p)) (a1Pt p) := by
  unfold a1Pt
  split_ifs with h
  · have h2 : 2 ≤ fx p := by
      have := fx_le_iff.mpr h
      rwa [fx_two_mul, fx_ONE, mul_one] at this
    unfold A1c
    split_ifs with h3
    · exact absurd h3 (not_lt.mpr h2)
    · exact ivMem_pi
  · have h2 : fx p < 2 := by
      have := fx_lt_iff.mpr (lt_of_not_ge h)
      rwa [fx_two_mul, fx_ONE, mul_one] at this
    unfold A1c a1f
    split_ifs with h3
    swap
    · exact absurd h2 h3
    have hh : ivMem (fx p / 2) (Iv.div2e (Iv.pt p) 1) := by
      have := Iv.mem_div2e (Iv.mem_pt p) 1
      simpa using this
    have hac := acosIv_spec hh
    have hs : ivMem (√(4 - fx p ^ 2)) (Iv.sqrt (Iv.sub (Iv.int 4) (Iv.sqr (Iv.pt p)))) := by
      have := Iv.mem_sqrt (Iv.mem_sub (Iv.mem_int 4) (Iv.mem_sqr (Iv.mem_pt p)))
      simpa using this
    have := Iv.mem_add (Iv.mem_sub ivMem_pi (Iv.mem_mul2e hac 1)) (Iv.mem_mul hh hs)
    convert this using 1
    ring

/-- `a1Iv` encloses `A_1` on a nonnegative point of the interval (`A_1` is increasing) -/
theorem a1Iv_bounds {x : ℝ} {r : Iv} (hx : ivMem x r) (h0 : 0 ≤ x) :
    fx (a1Iv r).lo ≤ A1c x ∧ A1c x ≤ fx (a1Iv r).hi := by
  obtain ⟨hx1, hx2⟩ := ivMem_iff.mp hx
  have hm := A1c_mono
  unfold a1Iv
  dsimp only
  have f1 : 0 ≤ fx (max r.lo 0) := by rw [fx_max]; exact le_max_of_le_right (by unfold fx; simp)
  have f2 : 0 ≤ fx (max r.hi 0) := by rw [fx_max]; exact le_max_of_le_right (by unfold fx; simp)
  have hlx : fx (max r.lo 0) ≤ x := by
    rw [fx_max]; exact max_le hx1 (by unfold fx; simpa using h0)
  have hxh : x ≤ fx (max r.hi 0) := by rw [fx_max]; exact le_max_of_le_left hx2
  constructor
  · exact (ivMem_lo_le (a1Pt_spec _)).trans (hm f1 h0 hlx)
  · exact (hm h0 f2 hxh).trans (ivMem_hi_le (a1Pt_spec _))

/-! ## reverse rounding bounds -/

lemma lt_shrD_add_one (a : ℤ) (n : ℕ) : (a : ℝ) / 2 ^ n < ((shrD a n : ℤ) : ℝ) + 1 := by
  unfold shrD
  rw [Int.shiftRight_eq_div_pow]
  have h2 : (0 : ℤ) < 2 ^ n := by positivity
  have := Int.lt_ediv_add_one_mul_self a h2
  rw [div_lt_iff₀ (by positivity)]
  exact_mod_cast this

lemma shrU_lt_add_one (a : ℤ) (n : ℕ) : ((shrU a n : ℤ) : ℝ) < (a : ℝ) / 2 ^ n + 1 := by
  have h := lt_shrD_add_one (-a) n
  unfold shrD at h
  unfold shrU
  rw [Int.cast_neg]
  push_cast at h
  rw [neg_div] at h
  linarith

lemma lt_divD_add_one (a b : ℤ) (hb : 0 < b) : (a : ℝ) / b < ((divD a b : ℤ) : ℝ) + 1 := by
  unfold divD
  have := Int.lt_ediv_add_one_mul_self a hb
  rw [div_lt_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast this

lemma divU_lt_add_one (a b : ℤ) (hb : 0 < b) : ((divU a b : ℤ) : ℝ) < (a : ℝ) / b + 1 := by
  have h := lt_divD_add_one (-a) b hb
  unfold divD at h
  unfold divU
  rw [Int.cast_neg]
  push_cast at h
  rw [neg_div] at h
  linarith

end BHH.W2.TabB
