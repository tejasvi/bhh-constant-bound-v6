/-
T8: `SectorCen`: the centroid of a sector is `secCentroid`, and the mean of `|w - cen|²` over the
sector is `(r1² + r2²)/2 - secRho²` (from the polar integrals of `W2/GeoPolar.lean`).
-/
import W2.TabProps
import W2.GeoSector

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W2

open BHH

theorem sectorCen : SectorCen := by
  intro r1 r2 a b h
  obtain ⟨hr1, h12, ha, hab, hb, hw⟩ := h
  have hV := area_pcell hr1 h12.le ha hab.le hb
  have hI1 := integral_pcell_fst hr1 h12.le ha hab.le hb
  have hI2 := integral_pcell_snd hr1 h12.le ha hab.le hb
  rw [← sector_eq_pcell] at hV hI1 hI2
  have hd : 0 < r2 ^ 2 - r1 ^ 2 := by nlinarith
  have hh : 0 < (b - a) / 2 := by linarith
  have hVp : 0 < (r2 ^ 2 - r1 ^ 2) / 2 * (b - a) := by positivity
  -- sum-to-product
  have hs : Real.sin b - Real.sin a = 2 * Real.sin ((b - a) / 2) * Real.cos ((a + b) / 2) := by
    rw [Real.sin_sub_sin]; ring_nf
  have hc : Real.cos a - Real.cos b = 2 * Real.sin ((b - a) / 2) * Real.sin ((a + b) / 2) := by
    rw [Real.cos_sub_cos]
    have : Real.sin ((a - b) / 2) = -Real.sin ((b - a) / 2) := by rw [← Real.sin_neg]; ring_nf
    rw [this]; ring_nf
  have hcen : cen (sector r1 r2 a b) = secCentroid r1 r2 a b := by
    unfold cen secCentroid secRho
    rw [hV, hI1, hI2, hs, hc]
    refine Prod.ext ?_ ?_
    · simp only; field_simp
    · simp only; field_simp
  refine ⟨hcen, ?_⟩
  have hM := integral_pcell_sqDist hr1 h12.le ha hab.le hb (cen (sector r1 r2 a b))
  rw [← sector_eq_pcell] at hM
  set C := cen (sector r1 r2 a b) with hC
  set V := (volume (sector r1 r2 a b)).toReal with hVdef
  have hV0 : V ≠ 0 := by rw [hV]; exact hVp.ne'
  have hC1 : (r2 ^ 3 - r1 ^ 3) / 3 * (Real.sin b - Real.sin a) = V * C.1 := by
    rw [← hI1, hC]; unfold cen; simp only; rw [← hVdef]; field_simp
  have hC2 : (r2 ^ 3 - r1 ^ 3) / 3 * (Real.cos a - Real.cos b) = V * C.2 := by
    rw [← hI2, hC]; unfold cen; simp only; rw [← hVdef]; field_simp
  rw [hM, hC1, hC2, ← hV]
  have hCC : C.1 ^ 2 + C.2 ^ 2 = secRho r1 r2 a b ^ 2 := by
    rw [hcen]; unfold secCentroid; simp only
    have := Real.cos_sq_add_sin_sq ((a + b) / 2)
    linear_combination secRho r1 r2 a b ^ 2 * this
  have hQ : V⁻¹ * ((r2 ^ 4 - r1 ^ 4) / 4 * (b - a)) = (r1 ^ 2 + r2 ^ 2) / 2 := by
    have hd' : r2 ^ 2 - r1 ^ 2 ≠ 0 := hd.ne'
    have hba : b - a ≠ 0 := by linarith
    rw [hV, show r2 ^ 4 - r1 ^ 4 = (r2 ^ 2 - r1 ^ 2) * (r1 ^ 2 + r2 ^ 2) by ring]
    field_simp
    ring
  have e : V⁻¹ * ((r2 ^ 4 - r1 ^ 4) / 4 * (b - a) - 2 * C.1 * (V * C.1) - 2 * C.2 * (V * C.2) +
      (C.1 ^ 2 + C.2 ^ 2) * V) = V⁻¹ * ((r2 ^ 4 - r1 ^ 4) / 4 * (b - a)) - (C.1 ^ 2 + C.2 ^ 2) := by
    field_simp; ring
  rw [e, hQ, hCC]

end BHH.W2
