/-
Module G: the hull of a sector (`SectorHull`): every point of a segment from the centroid to a point
of the sector is `ρ u(φ)` with `r1 cos((b - a)/2) ≤ ρ ≤ r2` and `a ≤ φ ≤ b`.
Proof in coordinates rotated by the bisector angle `m = (a + b)/2`: the point is `(X, Y)` with
`X = (1 - s) R + s ρ_z cos δ ≥ r1 cos h`, `|Y| = s ρ_z |sin δ| ≤ X tan h` (`δ = φ_z - m`, `|δ| < h = (b - a)/2`), and
`X² + Y² ≤ ((1 - s) R + s ρ_z)² ≤ r2²`, where `R = secRho ∈ [r1 cos h, r2]`.
-/
import W2.GeoProps

open MeasureTheory Set Real

noncomputable section

namespace BHH.W2

open BHH

/-- the centroid radius lies in `[r1 cos h, r2]` and is positive -/
lemma secRho_bounds {r1 r2 a b : ℝ} (h : SecOK r1 r2 a b) :
    r1 * Real.cos ((b - a) / 2) ≤ secRho r1 r2 a b ∧ secRho r1 r2 a b ≤ r2 ∧ 0 < secRho r1 r2 a b := by
  obtain ⟨hr1, h12, ha, hab, hb, hw⟩ := h
  have hh0 : 0 < (b - a) / 2 := by linarith
  have hh1 : (b - a) / 2 ≤ π / 4 := by linarith
  have hsin : 0 < Real.sin ((b - a) / 2) := Real.sin_pos_of_pos_of_lt_pi hh0 (by linarith [Real.pi_pos])
  have hsinle : Real.sin ((b - a) / 2) ≤ (b - a) / 2 := Real.sin_le hh0.le
  have htan : (b - a) / 2 < Real.tan ((b - a) / 2) := Real.lt_tan hh0 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos ((b - a) / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsinc1 : Real.cos ((b - a) / 2) ≤ Real.sin ((b - a) / 2) / ((b - a) / 2) := by
    rw [le_div_iff₀ hh0]
    rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hcos] at htan
    linarith
  have hsinc2 : Real.sin ((b - a) / 2) / ((b - a) / 2) ≤ 1 := by rw [div_le_one hh0]; exact hsinle
  have hsinc0 : 0 < Real.sin ((b - a) / 2) / ((b - a) / 2) := div_pos hsin hh0
  have hd : 0 < r2 ^ 2 - r1 ^ 2 := by nlinarith
  have hn : 0 < r2 ^ 3 - r1 ^ 3 := by nlinarith [sq_nonneg (r2 - r1), sq_nonneg r1, sq_nonneg r2]
  have hQe : 2 / 3 * ((r2 ^ 3 - r1 ^ 3) / (r2 ^ 2 - r1 ^ 2)) = 2 * (r2 ^ 3 - r1 ^ 3) / (3 * (r2 ^ 2 - r1 ^ 2)) := by
    field_simp
  have hQ1 : r1 ≤ 2 / 3 * ((r2 ^ 3 - r1 ^ 3) / (r2 ^ 2 - r1 ^ 2)) := by
    rw [hQe, le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sq_nonneg (r2 - r1)) (by linarith : (0 : ℝ) ≤ 2 * r2 + r1)]
  have hQ2 : 2 / 3 * ((r2 ^ 3 - r1 ^ 3) / (r2 ^ 2 - r1 ^ 2)) ≤ r2 := by
    rw [hQe, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sq_nonneg (r2 - r1)) (by linarith : (0 : ℝ) ≤ r2 + 2 * r1)]
  have hQ0 : 0 < 2 / 3 * ((r2 ^ 3 - r1 ^ 3) / (r2 ^ 2 - r1 ^ 2)) := by positivity
  unfold secRho
  refine ⟨?_, ?_, mul_pos hQ0 hsinc0⟩
  · exact mul_le_mul hQ1 hsinc1 hcos.le hQ0.le
  · calc 2 / 3 * ((r2 ^ 3 - r1 ^ 3) / (r2 ^ 2 - r1 ^ 2)) * (Real.sin ((b - a) / 2) / ((b - a) / 2))
        ≤ r2 * 1 := mul_le_mul hQ2 hsinc2 hsinc0.le (by linarith)
      _ = r2 := mul_one r2

lemma hull_rad_aux {s R ρz r2 cδ : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hR0 : 0 ≤ R) (hR2 : R ≤ r2)
    (hρz0 : 0 ≤ ρz) (hρz2 : ρz ≤ r2) (hc1 : cδ ≤ 1) :
    (1 - s) ^ 2 * R ^ 2 + 2 * s * (1 - s) * R * (ρz * cδ) + s ^ 2 * ρz ^ 2 ≤ r2 ^ 2 := by
  have hc0 : 0 ≤ 2 * s * (1 - s) * R := by
    have : 0 ≤ 1 - s := by linarith
    positivity
  have h1 : 2 * s * (1 - s) * R * (ρz * cδ) ≤ 2 * s * (1 - s) * R * ρz := by
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc1 hρz0) hc0
    linarith
  have h2 : (1 - s) * R + s * ρz ≤ r2 := by
    linarith [mul_nonneg (sub_nonneg.2 hs1) (sub_nonneg.2 hR2), mul_nonneg hs0 (sub_nonneg.2 hρz2)]
  have h3 : 0 ≤ (1 - s) * R + s * ρz := by
    have := mul_nonneg (sub_nonneg.2 hs1) hR0
    have := mul_nonneg hs0 hρz0
    linarith
  have h4 := mul_le_mul h2 h2 h3 (by linarith)
  nlinarith [h1, h4]

theorem sectorHull_aux (r1 r2 a b : ℝ) (h : SecOK r1 r2 a b) (z : Pt) (hz : z ∈ sector r1 r2 a b) (s : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ ρ φ : ℝ, segPt (secCentroid r1 r2 a b) z s = (ρ * Real.cos φ, ρ * Real.sin φ) ∧
      r1 * Real.cos ((b - a) / 2) ≤ ρ ∧ ρ ≤ r2 ∧ a ≤ φ ∧ φ ≤ b := by
  obtain ⟨hR1, hR2, hR0⟩ := secRho_bounds h
  obtain ⟨hr1, h12, ha, hab, hb, hw⟩ := h
  obtain ⟨⟨ρz, φz⟩, ⟨hρz, hφz⟩, rfl⟩ := hz
  simp only [mem_Ioo] at hρz hφz
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨m, hm⟩ : ∃ m, m = (a + b) / 2 := ⟨_, rfl⟩
  obtain ⟨hh, hhh⟩ : ∃ hh, hh = (b - a) / 2 := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = secRho r1 r2 a b := ⟨_, rfl⟩
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = φz - m := ⟨_, rfl⟩
  rw [← hhh, ← hR] at hR1
  rw [← hR] at hR2 hR0
  have hh0 : 0 < hh := by rw [hhh]; linarith
  have hhpi : hh < π / 2 := by rw [hhh]; linarith [Real.pi_pos]
  have hδ1 : -hh < δ := by rw [hδdef, hm, hhh]; linarith
  have hδ2 : δ < hh := by rw [hδdef, hm, hhh]; linarith
  have hcosδ : Real.cos hh ≤ Real.cos δ := by
    rw [← Real.cos_abs δ]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg δ) (by linarith [Real.pi_pos])
      (abs_le.2 ⟨hδ1.le, hδ2.le⟩)
  have hcosh : 0 < Real.cos hh := Real.cos_pos_of_mem_Ioo ⟨by linarith, hhpi⟩
  have hcosδ0 : 0 < Real.cos δ := hcosh.trans_le hcosδ
  have hρz0 : 0 < ρz := hr1.trans_lt hρz.1
  -- rotated coordinates
  obtain ⟨P, hP⟩ : ∃ P, P = ρz * Real.cos δ := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, X = (1 - s) * R + s * P := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = s * (ρz * Real.sin δ) := ⟨_, rfl⟩
  have hpt : segPt (secCentroid r1 r2 a b) (polarCoord.symm (ρz, φz)) s =
      (X * Real.cos m - Y * Real.sin m, X * Real.sin m + Y * Real.cos m) := by
    have hφ : φz = m + δ := by rw [hδdef]; ring
    simp only [segPt, secCentroid, polarCoord_symm_apply, ← hm, ← hR]
    rw [hφ, Real.cos_add, Real.sin_add, hX, hY, hP]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]; ring
    · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]; ring
  -- `X ≥ r1 cos h` and `X > 0`
  have hP1 : r1 * Real.cos hh ≤ P := by rw [hP]; exact mul_le_mul hρz.1.le hcosδ hcosh.le hρz0.le
  have hP0 : 0 < P := by rw [hP]; exact mul_pos hρz0 hcosδ0
  have hX1 : r1 * Real.cos hh ≤ X := by
    have h1 : 0 ≤ (1 - s) * (R - r1 * Real.cos hh) := mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ s * (P - r1 * Real.cos hh) := mul_nonneg hs0 (by linarith)
    rw [hX]; nlinarith
  have hX0 : 0 < X := by
    rcases le_total R P with hRP | hRP
    · have : R ≤ X := by rw [hX]; nlinarith [mul_nonneg hs0 (sub_nonneg.2 hRP)]
      linarith
    · have : P ≤ X := by rw [hX]; nlinarith [mul_nonneg (sub_nonneg.2 hs1) (sub_nonneg.2 hRP)]
      linarith
  -- `|Y| ≤ X tan h`
  have htanδ : |Real.sin δ| ≤ Real.tan hh * Real.cos δ := by
    have habs : |δ| < hh := abs_lt.2 ⟨hδ1, hδ2⟩
    have ht : Real.tan |δ| ≤ Real.tan hh :=
      (Real.tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith [abs_nonneg δ]) hhpi habs).le
    have hca : Real.cos |δ| = Real.cos δ := Real.cos_abs δ
    have e : |Real.sin δ| = Real.tan |δ| * Real.cos δ := by
      rw [Real.tan_eq_sin_div_cos, hca, div_mul_cancel₀ _ hcosδ0.ne']
      rcases le_total 0 δ with hd | hd
      · rw [abs_of_nonneg hd, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hd (by linarith))]
      · rw [abs_of_nonpos hd, Real.sin_neg, abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le hd
          (by linarith))]
    rw [e]
    exact mul_le_mul_of_nonneg_right ht hcosδ0.le
  have htanh : 0 ≤ Real.tan hh := (Real.tan_pos_of_pos_of_lt_pi_div_two hh0 hhpi).le
  have hYX : |Y| ≤ Real.tan hh * X := by
    rw [hY, abs_mul, abs_mul, abs_of_nonneg hs0, abs_of_pos hρz0]
    have h1 : s * (ρz * |Real.sin δ|) ≤ s * (ρz * (Real.tan hh * Real.cos δ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htanδ hρz0.le) hs0
    have h2 : 0 ≤ Real.tan hh * ((1 - s) * R) := mul_nonneg htanh (mul_nonneg (by linarith) hR0.le)
    rw [hX, hP]
    nlinarith
  -- the angle
  obtain ⟨t, ht⟩ : ∃ t, t = Y / X := ⟨_, rfl⟩
  have htle : |t| ≤ Real.tan hh := by
    rw [ht, abs_div, abs_of_pos hX0, div_le_iff₀ hX0]
    linarith
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = Real.arctan t := ⟨_, rfl⟩
  have hψ1 : ψ ≤ hh := by
    have := Real.arctan_mono (le_trans (le_abs_self t) htle)
    rwa [Real.arctan_tan (by linarith) hhpi, ← hψ] at this
  have hψ2 : -hh ≤ ψ := by
    have := Real.arctan_mono (show -Real.tan hh ≤ t by linarith [neg_abs_le t])
    rwa [Real.arctan_neg, Real.arctan_tan (by linarith) hhpi, ← hψ] at this
  -- the radius
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = X * Real.sqrt (1 + t ^ 2) := ⟨_, rfl⟩
  have hsq : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hsq1 : 1 ≤ Real.sqrt (1 + t ^ 2) := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + t ^ 2 by nlinarith [sq_nonneg t])
    rwa [Real.sqrt_one] at this
  have hXc : ρ * Real.cos ψ = X := by
    rw [hρ, hψ, Real.cos_arctan, mul_assoc, mul_one_div_cancel hsq.ne', mul_one]
  have hYs : ρ * Real.sin ψ = Y := by
    rw [hρ, hψ, Real.sin_arctan, ht]
    field_simp
  have hρsq : ρ ^ 2 = X ^ 2 + Y ^ 2 := by
    rw [hρ, mul_pow, Real.sq_sqrt (by positivity), ht]
    field_simp
  refine ⟨ρ, m + ψ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpt, Real.cos_add, Real.sin_add, ← hXc, ← hYs]
    refine Prod.ext ?_ ?_
    · show ρ * Real.cos ψ * Real.cos m - ρ * Real.sin ψ * Real.sin m =
        ρ * (Real.cos m * Real.cos ψ - Real.sin m * Real.sin ψ)
      ring
    · show ρ * Real.cos ψ * Real.sin m + ρ * Real.sin ψ * Real.cos m =
        ρ * (Real.sin m * Real.cos ψ + Real.cos m * Real.sin ψ)
      ring
  · rw [← hhh]
    calc r1 * Real.cos hh ≤ X := hX1
      _ = X * 1 := (mul_one X).symm
      _ ≤ ρ := by rw [hρ]; exact mul_le_mul_of_nonneg_left hsq1 hX0.le
  · -- `ρ² = X² + Y² ≤ ((1 - s) R + s ρz)² ≤ r2²`
    have hcs : Real.cos δ ^ 2 + Real.sin δ ^ 2 = 1 := Real.cos_sq_add_sin_sq δ
    have e : X ^ 2 + Y ^ 2 =
        (1 - s) ^ 2 * R ^ 2 + 2 * s * (1 - s) * R * (ρz * Real.cos δ) + s ^ 2 * ρz ^ 2 := by
      rw [hX, hY, hP]; linear_combination s ^ 2 * ρz ^ 2 * hcs
    have hle : ρ ^ 2 ≤ r2 ^ 2 := by
      rw [hρsq, e]
      exact hull_rad_aux hs0 hs1 hR0.le hR2 hρz0.le hρz.2.le (Real.cos_le_one δ)
    have hρ0 : 0 ≤ ρ := by rw [hρ]; exact mul_nonneg hX0.le hsq.le
    exact (pow_le_pow_iff_left₀ hρ0 (by linarith) two_ne_zero).1 hle
  · have : a = m - hh := by rw [hm, hhh]; ring
    linarith
  · have : b = m + hh := by rw [hm, hhh]; ring
    linarith

end BHH.W2
