/-
Module G: the sector Props of `W2/GeoProps.lean`: `SectorArea` (G1), `SectorRadial` (G2),
`SectorMoments` (G3), `SectorHull` (G4), `GreenGradLe` (G5, in `W2/GeoGrad.lean`), `QuadBox` (G6).
-/
import W2.GeoPolar
import W2.GeoQuad
import W2.GeoHull
import W2.GeoGrad

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W2

open BHH

lemma sector_eq_pcell (r1 r2 a b : ℝ) : sector r1 r2 a b = pcell r1 r2 a b := rfl

lemma volume_sector_ne_top (r1 r2 a b : ℝ) (hr : 0 ≤ r1) : volume (sector r1 r2 a b) ≠ ⊤ := by
  have hb : Bornology.IsBounded (sector r1 r2 a b) := by
    refine (Metric.isBounded_closedBall (x := (0 : Pt)) (r := r2)).subset ?_
    rintro _ ⟨p, hp, rfl⟩
    simp only [mem_prod, mem_Ioo] at hp
    have hp1 : 0 < p.1 := hr.trans_lt hp.1.1
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff, Real.norm_eq_abs, Real.norm_eq_abs,
      polar_symm_fst, polar_symm_snd, abs_mul, abs_mul, abs_of_pos hp1]
    exact ⟨(mul_le_of_le_one_right hp1.le (abs_cos_le_one _)).trans hp.1.2.le,
      (mul_le_of_le_one_right hp1.le (abs_sin_le_one _)).trans hp.1.2.le⟩
  exact hb.measure_lt_top.ne

/-- (G1) -/
theorem sectorArea : SectorArea := by
  intro r1 r2 a b h
  obtain ⟨hr1, h12, ha, hab, hb, hw⟩ := h
  rw [← ENNReal.ofReal_toReal (volume_sector_ne_top r1 r2 a b hr1), sector_eq_pcell,
    area_pcell hr1 h12.le ha hab.le hb]
  congr 1
  ring

/-- (G2) -/
theorem sectorRadial : SectorRadial := by
  intro r1 r2 a b f h _
  obtain ⟨hr1, h12, ha, hab, hb, hw⟩ := h
  rw [sector_eq_pcell]
  have := integral_pcell_radial hr1 h12.le ha hab.le hb f
  unfold enorm2
  rw [this, mul_comm]
  congr 1
  exact intervalIntegral.integral_congr fun r _ => mul_comm r (f r)

/-- (G3) -/
theorem sectorMoments : SectorMoments := by
  intro r1 r2 a b h
  obtain ⟨hr1, h12, ha, hab, hb, hw⟩ := h
  rw [sector_eq_pcell]
  exact ⟨integral_pcell_fst hr1 h12.le ha hab.le hb, integral_pcell_snd hr1 h12.le ha hab.le hb,
    integral_pcell_sq hr1 h12.le ha hab.le hb⟩

/-- (G4) -/
theorem sectorHull : SectorHull := fun r1 r2 a b h z hz s hs => sectorHull_aux r1 r2 a b h z hz s hs

/-- (G6) -/
theorem quadBox : QuadBox := fun r1 r2 q1 q2 c1 c2 r q c hr1 hq1 hc1 hc2 hr hr' hq hq' hc hc' =>
  quadBox_aux r1 r2 q1 q2 c1 c2 r q c hr1 hq1 hc1 hc2 hr hr' hq hq' hc hc'

end BHH.W2
