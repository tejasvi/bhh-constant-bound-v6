/-
Geometry for the entry soundness: integrals of `A_1` over sectors, integrals over products of sectors of functions
of one coordinate, and the distance bounds along the segments from the rounded centroids (hull of a sector).
-/
import W2.TabProps
import W2.GeoSector
import W2.Euc

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W2

open BHH

/-! ## `A1c` is continuous -/

lemma A1c_eq_min {r : ℝ} : A1c r = a1f (min r 2) := by
  unfold A1c
  split_ifs with h
  · rw [min_eq_left h.le]
  · rw [min_eq_right (not_lt.mp h), a1f_two]

lemma A1c_continuousOn : ContinuousOn A1c (Ici 0) := by
  have h : EqOn A1c (fun r => a1f (min r 2)) (Ici 0) := fun r _ => A1c_eq_min
  refine ContinuousOn.congr ?_ h
  refine a1f_continuousOn.comp (continuous_id.min continuous_const).continuousOn ?_
  intro r hr
  exact ⟨le_min hr (by norm_num), min_le_right _ _⟩

/-! ## Integrals over sectors and products of sectors -/

lemma volume_sector_toReal {r1 r2 a b : ℝ} (h : SecOK r1 r2 a b) :
    (volume (sector r1 r2 a b)).toReal = (r2 ^ 2 - r1 ^ 2) * (b - a) / 2 := by
  rw [sectorArea r1 r2 a b h, ENNReal.toReal_ofReal]
  obtain ⟨h0, h1, -, h3, -, -⟩ := h
  have : 0 ≤ r2 ^ 2 - r1 ^ 2 := by nlinarith
  have : 0 ≤ b - a := by linarith
  positivity

lemma volume_sector_pos {r1 r2 a b : ℝ} (h : SecOK r1 r2 a b) : 0 < (volume (sector r1 r2 a b)).toReal := by
  rw [volume_sector_toReal h]
  obtain ⟨h0, h1, -, h3, -, -⟩ := h
  have : 0 < r2 ^ 2 - r1 ^ 2 := by nlinarith
  have : 0 < b - a := by linarith
  positivity

/-- `∫_S A_1 = |S| · meanA1(r1, r2)` (under Green's formula, through `A1Radial`). -/
lemma integral_A1_sector (hG : GreenFormula) (hA1 : A1Radial) {r1 r2 a b : ℝ} (h : SecOK r1 r2 a b) :
    ∫ z in sector r1 r2 a b, A1 z = (volume (sector r1 r2 a b)).toReal * meanA1 r1 r2 := by
  have e : (fun z => A1 z) = fun z => A1c (enorm2 z) := funext fun z => hA1 hG z
  rw [e, sectorRadial r1 r2 a b A1c h (A1c_continuousOn.mono fun r hr => le_trans h.1 hr.1),
    volume_sector_toReal h]
  unfold meanA1
  obtain ⟨h0, h1, -, -, -, -⟩ := h
  have : r2 ^ 2 - r1 ^ 2 ≠ 0 := by nlinarith
  field_simp

lemma setIntegral_snd' (S S' : Set Pt) (f : Pt → ℝ) :
    ∫ p in S ×ˢ S', f p.2 = (volume S).toReal * ∫ z in S', f z := by
  have h := setIntegral_prod_mul (μ := (volume : Measure Pt)) (ν := (volume : Measure Pt))
    (fun _ => (1 : ℝ)) f S S'
  simp only [one_mul] at h
  rw [Measure.volume_eq_prod, h, setIntegral_const, smul_eq_mul, mul_one]
  rfl

lemma setIntegral_fst' (S S' : Set Pt) (f : Pt → ℝ) :
    ∫ p in S ×ˢ S', f p.1 = (volume S').toReal * ∫ w in S, f w := by
  have h := setIntegral_prod_mul (μ := (volume : Measure Pt)) (ν := (volume : Measure Pt))
    f (fun _ => (1 : ℝ)) S S'
  simp only [mul_one] at h
  rw [Measure.volume_eq_prod, h, setIntegral_const, smul_eq_mul, mul_one, mul_comm]
  rfl

/-! ## Segments from rounded centroids -/

lemma segPt_eq (c y : Pt) (t : ℝ) : segPt c y t = c + t • (y - c) := rfl

/-- A point of the segment from a rounded centroid `m` (`|C - m| ≤ e`) to `w ∈ S` has norm within `e` of the
polar box of the hull: `r1 cos(h/2) - e ≤ |m + t (w - m)| ≤ r2 + e`, and it is within `e` of a hull point
`ρ u(φ)`, `r1 cos((b-a)/2) ≤ ρ ≤ r2`, `a ≤ φ ≤ b`. -/
lemma seg_hull {r1 r2 a b : ℝ} (h : SecOK r1 r2 a b) {w : Pt} (hw : w ∈ sector r1 r2 a b) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (m : Pt) {e : ℝ} (hm : edist2 (secCentroid r1 r2 a b) m ≤ e) :
    ∃ ρ φ : ℝ, r1 * Real.cos ((b - a) / 2) ≤ ρ ∧ ρ ≤ r2 ∧ a ≤ φ ∧ φ ≤ b ∧
      enorm2 ((m + t • (w - m)) - (ρ * Real.cos φ, ρ * Real.sin φ)) ≤ e := by
  obtain ⟨ρ, φ, hW, hρ1, hρ2, hφ1, hφ2⟩ := sectorHull r1 r2 a b h w hw t ht
  refine ⟨ρ, φ, hρ1, hρ2, hφ1, hφ2, ?_⟩
  rw [← hW, segPt_eq]
  have e1 : (m + t • (w - m)) - (secCentroid r1 r2 a b + t • (w - secCentroid r1 r2 a b)) =
      (1 - t) • (m - secCentroid r1 r2 a b) := by
    ext <;> simp <;> ring
  rw [e1, enorm2_smul, abs_of_nonneg (by linarith [ht.2])]
  rw [edist2_comm, edist2_eq] at hm
  calc (1 - t) * enorm2 (m - secCentroid r1 r2 a b) ≤ 1 * enorm2 (m - secCentroid r1 r2 a b) :=
        mul_le_mul_of_nonneg_right (by linarith [ht.1]) (enorm2_nonneg _)
    _ ≤ e := by rw [one_mul]; exact hm

lemma cos_half_nonneg {r1 r2 a b : ℝ} (h : SecOK r1 r2 a b) : 0 ≤ Real.cos ((b - a) / 2) := by
  obtain ⟨-, -, -, h3, -, h5⟩ := h
  apply Real.cos_nonneg_of_mem_Icc
  constructor <;> linarith [Real.pi_pos]

/-- Norm bounds along the segment from a rounded centroid. -/
lemma seg_norm {r1 r2 a b : ℝ} (h : SecOK r1 r2 a b) {w : Pt} (hw : w ∈ sector r1 r2 a b) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (m : Pt) {e : ℝ} (hm : edist2 (secCentroid r1 r2 a b) m ≤ e) :
    r1 * Real.cos ((b - a) / 2) - e ≤ enorm2 (m + t • (w - m)) ∧ enorm2 (m + t • (w - m)) ≤ r2 + e := by
  obtain ⟨ρ, φ, hρ1, hρ2, -, -, hd⟩ := seg_hull h hw ht m hm
  have hρ0 : 0 ≤ ρ := le_trans (mul_nonneg h.1 (cos_half_nonneg h)) hρ1
  have hab := abs_enorm2_sub_le (m + t • (w - m)) (ρ * Real.cos φ, ρ * Real.sin φ)
  rw [enorm2_polar ρ φ hρ0] at hab
  have := (abs_le.mp (hab.trans hd))
  constructor <;> linarith [this.1, this.2]

end BHH.W2
