/-
Module C: Prop 3.8 (geometric part: enlarged disks) and `A(y) ≥ π`.
-/
import BHH.Box.Props

open MeasureTheory Set Real
open scoped ENNReal Pointwise

noncomputable section

namespace BHH

/-! ## Euclidean distance in the plane -/

lemma sqDist_nonneg (a b : Pt) : 0 ≤ sqDist a b := by unfold sqDist; positivity

lemma edist2_nonneg (a b : Pt) : 0 ≤ edist2 a b := Real.sqrt_nonneg _

lemma edist2_sq (a b : Pt) : edist2 a b ^ 2 = sqDist a b := Real.sq_sqrt (sqDist_nonneg a b)

lemma edist2_comm (a b : Pt) : edist2 a b = edist2 b a := by
  unfold edist2 sqDist; ring_nf

/-- the triangle inequality for the Euclidean distance in the plane -/
lemma edist2_triangle (a b c : Pt) : edist2 a c ≤ edist2 a b + edist2 b c := by
  have h1 := edist2_nonneg a b
  have h2 := edist2_nonneg b c
  rw [← sq_le_sq₀ (edist2_nonneg a c) (add_nonneg h1 h2), edist2_sq, add_sq, edist2_sq, edist2_sq]
  -- Cauchy-Schwarz in the plane: `⟨u, w⟩ ≤ |u| |w|`
  set u1 := a.1 - b.1; set u2 := a.2 - b.2; set w1 := b.1 - c.1; set w2 := b.2 - c.2
  have hcs : u1 * w1 + u2 * w2 ≤ edist2 a b * edist2 b c := by
    have hsq : (u1 * w1 + u2 * w2) ^ 2 ≤ (edist2 a b * edist2 b c) ^ 2 := by
      rw [mul_pow, edist2_sq, edist2_sq]
      unfold sqDist
      nlinarith [sq_nonneg (u1 * w2 - u2 * w1)]
    exact abs_le_of_sq_le_sq' hsq (mul_nonneg h1 h2) |>.2
  have e : sqDist a c = sqDist a b + 2 * (u1 * w1 + u2 * w2) + sqDist b c := by
    unfold sqDist; ring
  rw [e]
  linarith

lemma mem_disk_iff_edist2 {z a : Pt} {r : ℝ} (hr : 0 ≤ r) : z ∈ disk a r ↔ edist2 z a ≤ r := by
  rw [disk, Set.mem_ofPred_eq, ← edist2_sq, sq_le_sq₀ (edist2_nonneg z a) hr]

/-! ## Areas of disks and of their unions -/

lemma volume_disk (a : Pt) {r : ℝ} (hr : 0 ≤ r) : volume (disk a r) = ENNReal.ofReal (π * r ^ 2) := by
  have hpre : Complex.measurableEquivRealProd ⁻¹' (disk a r) = Metric.closedBall (⟨a.1, a.2⟩ : ℂ) r := by
    ext w
    simp only [Set.mem_preimage, Complex.measurableEquivRealProd_apply, disk, sqDist, Set.mem_ofPred_eq,
      Metric.mem_closedBall, Complex.dist_eq]
    rw [← sq_le_sq₀ (norm_nonneg _) hr, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    constructor <;> intro h <;> nlinarith [h]
  rw [← Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv, hpre,
    Complex.volume_closedBall, ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
    ← ENNReal.ofReal_mul (by positivity)]
  ring_nf

lemma volume_disk_ne_top (a : Pt) (r : ℝ) : volume (disk a r) ≠ ⊤ := by
  rcases le_or_gt 0 r with hr | hr
  · rw [volume_disk a hr]; exact ENNReal.ofReal_ne_top
  · -- `disk a r = disk a |r|`
    have : disk a r = disk a (-r) := by ext z; simp [disk]
    rw [this, volume_disk a (by linarith)]; exact ENNReal.ofReal_ne_top

lemma volume_iUnion_disk_ne_top {k : ℕ} (c : Fin k → Pt) (r : ℝ) :
    volume (⋃ i, disk (c i) r) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun i _ => volume_disk_ne_top (c i) r)
    (measure_iUnion_fintype_le volume _)

/-- Prop 3.8, geometric part -/
theorem enlargedDisksProp : EnlargedDisksProp := by
  intro k y c ε hyc
  refine ⟨volume_iUnion_disk_ne_top c (1 + ε), ?_⟩
  unfold unionArea
  refine ENNReal.toReal_mono (volume_iUnion_disk_ne_top c (1 + ε)) (measure_mono ?_)
  refine Set.iUnion_subset fun i z hz => Set.mem_iUnion.2 ⟨i, ?_⟩
  have hε : 0 ≤ ε := (edist2_nonneg _ _).trans (hyc i)
  rw [mem_disk_iff_edist2 (by linarith)]
  rw [mem_disk_iff_edist2 zero_le_one] at hz
  calc edist2 z (c i) ≤ edist2 z (y i) + edist2 (y i) (c i) := edist2_triangle _ _ _
    _ ≤ 1 + ε := add_le_add hz (hyc i)

/-- `A(y) ≥ π` -/
theorem unionAreaGePiProp : UnionAreaGePiProp := by
  intro k y hk
  unfold unionArea
  have h0 : (volume (disk (y ⟨0, hk⟩) 1)).toReal = π := by
    rw [volume_disk _ zero_le_one, one_pow, mul_one, ENNReal.toReal_ofReal Real.pi_pos.le]
  rw [← h0]
  exact ENNReal.toReal_mono (volume_iUnion_disk_ne_top y 1)
    (measure_mono (Set.subset_iUnion (fun i => disk (y i) 1) ⟨0, hk⟩))

/-- unions of disks over two families with the same set of centres agree -/
lemma iUnion_disk_congr {k l : ℕ} (c : Fin k → Pt) (c' : Fin l → Pt) (r : ℝ)
    (h1 : ∀ i, ∃ j, c i = c' j) (h2 : ∀ j, ∃ i, c' j = c i) :
    (⋃ i, disk (c i) r) = ⋃ j, disk (c' j) r := by
  apply Set.Subset.antisymm
  · refine Set.iUnion_subset fun i => ?_
    obtain ⟨j, hj⟩ := h1 i
    rw [hj]; exact Set.subset_iUnion (fun j => disk (c' j) r) j
  · refine Set.iUnion_subset fun j => ?_
    obtain ⟨i, hi⟩ := h2 j
    rw [hi]; exact Set.subset_iUnion (fun i => disk (c i) r) i

/-! ## Monotonicity in the radius and scaling -/

lemma disk_mono (a : Pt) {ρ ρ' : ℝ} (h0 : 0 ≤ ρ) (h : ρ ≤ ρ') : disk a ρ ⊆ disk a ρ' := fun z hz => by
  simp only [disk, Set.mem_ofPred_eq] at hz ⊢
  exact hz.trans (pow_le_pow_left₀ h0 h 2)

/-- the area of a union of disks is nondecreasing in the radius -/
lemma volume_iUnion_disk_mono {k : ℕ} (c : Fin k → Pt) {ρ ρ' : ℝ} (h0 : 0 ≤ ρ) (h : ρ ≤ ρ') :
    volume (⋃ i, disk (c i) ρ) ≤ volume (⋃ i, disk (c i) ρ') :=
  measure_mono (Set.iUnion_mono fun i => disk_mono (c i) h0 h)

lemma volume_iUnion_disk_mono_toReal {k : ℕ} (c : Fin k → Pt) {ρ ρ' : ℝ} (h0 : 0 ≤ ρ) (h : ρ ≤ ρ') :
    (volume (⋃ i, disk (c i) ρ)).toReal ≤ (volume (⋃ i, disk (c i) ρ')).toReal :=
  ENNReal.toReal_mono (volume_iUnion_disk_ne_top c ρ') (volume_iUnion_disk_mono c h0 h)

lemma sqDist_smul (r : ℝ) (a b : Pt) : sqDist (r • a) (r • b) = r ^ 2 * sqDist a b := by
  simp only [sqDist, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- the disks of radius `R` are the images of the unit disks around `c/R` under `z ↦ R z` -/
lemma iUnion_disk_eq_smul {k : ℕ} (c : Fin k → Pt) {R : ℝ} (hR : 0 < R) :
    (⋃ i, disk (c i) R) = R • ⋃ i, disk (R⁻¹ • c i) 1 := by
  ext z
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hR.ne', Set.mem_iUnion, Set.mem_iUnion]
  refine exists_congr fun i => ?_
  simp only [disk, Set.mem_ofPred_eq]
  rw [sqDist_smul, one_pow, inv_pow]
  constructor
  · intro hz
    calc (R ^ 2)⁻¹ * sqDist z (c i) ≤ (R ^ 2)⁻¹ * R ^ 2 := mul_le_mul_of_nonneg_left hz (by positivity)
      _ = 1 := inv_mul_cancel₀ (by positivity)
  · intro hz
    have hR2 : 0 < R ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hz hR2.le
    rwa [← mul_assoc, mul_inv_cancel₀ hR2.ne', one_mul, mul_one] at this

/-- scaling: `area(⋃ B(c_i, R)) = R² · area(⋃ B(c_i/R, 1))` -/
lemma volume_iUnion_disk_scale {k : ℕ} (c : Fin k → Pt) {R : ℝ} (hR : 0 < R) :
    volume (⋃ i, disk (c i) R) = ENNReal.ofReal (R ^ 2) * volume (⋃ i, disk (R⁻¹ • c i) 1) := by
  rw [iUnion_disk_eq_smul c hR, Measure.addHaar_smul, Module.finrank_prod, Module.finrank_self,
    show (1 + 1 : ℕ) = 2 from rfl, abs_of_pos (pow_pos hR 2)]

/-- scaling, real form: `area(⋃ B(c_i, R)) = R² A(c/R)` -/
lemma iUnion_disk_area_scale {k : ℕ} (c : Fin k → Pt) {R : ℝ} (hR : 0 < R) :
    (volume (⋃ i, disk (c i) R)).toReal = R ^ 2 * unionArea (fun i => R⁻¹ • c i) := by
  rw [volume_iUnion_disk_scale c hR, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), unionArea]

end BHH
