/-
Module D: the polar cells (measurable, bounded, inside the right half-plane, pairwise disjoint),
the product cells, and measurability and bounds of `A1`, `A2`.
-/
import W2.DiscMeas

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W2

/-! ## Areas of disks -/

lemma volume_disk' (a : Pt) {r : ℝ} (hr : 0 ≤ r) : volume (disk a r) = ENNReal.ofReal (π * r ^ 2) := by
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

lemma volume_disk_one (a : Pt) : volume (disk a 1) = ENNReal.ofReal π := by
  rw [volume_disk' a zero_le_one, one_pow, mul_one]

/-! ## `A1`, `A2`: measurability and bounds -/

lemma measurableSet_disk_rel : MeasurableSet {q : Pt × Pt | sqDist q.2 q.1 ≤ 1 ^ 2} :=
  measurableSet_le (by unfold sqDist; fun_prop) measurable_const

lemma measurable_A1 : Measurable A1 := by
  have hE : MeasurableSet {q : Pt × Pt | q.2 ∈ disk q.1 1 \ disk 0 1} := by
    have h1 : MeasurableSet {q : Pt × Pt | sqDist q.2 q.1 ≤ 1 ^ 2} := measurableSet_disk_rel
    have h2 : MeasurableSet {q : Pt × Pt | sqDist q.2 0 ≤ 1 ^ 2} :=
      measurableSet_le (by unfold sqDist; fun_prop) measurable_const
    exact h1.inter h2.compl
  have := measurable_measure_prodMk_left (ν := (volume : Measure Pt)) hE
  exact this.ennreal_toReal

lemma measurable_A2 : Measurable fun q : Pt × Pt => A2 q.1 q.2 := by
  have hE : MeasurableSet {r : (Pt × Pt) × Pt | r.2 ∈ disk r.1.2 1 \ (disk 0 1 ∪ disk (-r.1.1) 1)} := by
    have h1 : MeasurableSet {r : (Pt × Pt) × Pt | sqDist r.2 r.1.2 ≤ 1 ^ 2} :=
      measurableSet_le (by unfold sqDist; fun_prop) measurable_const
    have h2 : MeasurableSet {r : (Pt × Pt) × Pt | sqDist r.2 0 ≤ 1 ^ 2} :=
      measurableSet_le (by unfold sqDist; fun_prop) measurable_const
    have h3 : MeasurableSet {r : (Pt × Pt) × Pt | sqDist r.2 (-r.1.1) ≤ 1 ^ 2} :=
      measurableSet_le (by unfold sqDist; fun_prop) measurable_const
    exact h1.inter (h2.union h3).compl
  have := measurable_measure_prodMk_left (ν := (volume : Measure Pt)) hE
  exact this.ennreal_toReal

lemma A1_nonneg (z : Pt) : 0 ≤ A1 z := ENNReal.toReal_nonneg

lemma A1_le_pi (z : Pt) : A1 z ≤ π := by
  unfold A1
  have h : volume (disk z 1 \ disk 0 1) ≤ ENNReal.ofReal π := (volume_disk_one z) ▸ measure_mono sdiff_subset
  rw [← ENNReal.toReal_ofReal Real.pi_pos.le]
  exact ENNReal.toReal_mono ENNReal.ofReal_ne_top h

lemma A2_nonneg (w z : Pt) : 0 ≤ A2 w z := ENNReal.toReal_nonneg

lemma A2_le_pi (w z : Pt) : A2 w z ≤ π := by
  unfold A2
  have h : volume (disk z 1 \ (disk 0 1 ∪ disk (-w) 1)) ≤ ENNReal.ofReal π :=
    (volume_disk_one z) ▸ measure_mono sdiff_subset
  rw [← ENNReal.toReal_ofReal Real.pi_pos.le]
  exact ENNReal.toReal_mono ENNReal.ofReal_ne_top h

/-! ## The polar grid -/

namespace GridR

variable (g : GridR)

lemma rad_nonneg (j : ℕ) : 0 ≤ g.rad j := by
  unfold rad; split_ifs
  · positivity
  · positivity

lemma rad_mono : Monotone g.rad := by
  intro i j hij
  unfold rad
  split_ifs with hi hj hj
  · exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (Nat.cast_nonneg _)
  · have h1 : (i : ℝ) / g.N1 ≤ 1 := by
      rcases Nat.eq_zero_or_pos g.N1 with h0 | h0
      · simp [h0]
      · rw [div_le_one (by exact_mod_cast h0)]; exact_mod_cast hi
    have : (0 : ℝ) ≤ ((j - g.N1 : ℕ) : ℝ) / g.N2 := by positivity
    linarith
  · omega
  · have : ((i - g.N1 : ℕ) : ℝ) ≤ ((j - g.N1 : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le_sub_right hij _
    have := div_le_div_of_nonneg_right this (Nat.cast_nonneg g.N2)
    linarith

lemma ang_lt (hNT : 0 < g.NT) {i j : ℕ} (hij : i < j) : g.ang i < g.ang j := by
  unfold ang
  have hN : (0 : ℝ) < g.NT := by exact_mod_cast hNT
  have : (i : ℝ) * π / g.NT < (j : ℝ) * π / g.NT := by
    apply div_lt_div_of_pos_right _ hN
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hij) Real.pi_pos
  linarith

lemma ang_mono (hNT : 0 < g.NT) : Monotone g.ang := by
  intro i j hij
  rcases eq_or_lt_of_le hij with h | h
  · rw [h]
  · exact (g.ang_lt hNT h).le

lemma ang_ge (hNT : 0 < g.NT) (i : ℕ) : -(π / 2) ≤ g.ang i := by
  unfold ang
  have : (0 : ℝ) ≤ (i : ℝ) * π / g.NT := by positivity
  linarith

lemma ang_le (hNT : 0 < g.NT) {i : ℕ} (hi : i ≤ g.NT) : g.ang i ≤ π / 2 := by
  unfold ang
  have hN : (0 : ℝ) < g.NT := by exact_mod_cast hNT
  have : (i : ℝ) * π / g.NT ≤ π := by
    rw [div_le_iff₀ hN]; nlinarith [Real.pi_pos, (by exact_mod_cast hi : (i : ℝ) ≤ g.NT)]
  linarith

/-- the open polar box of a cell -/
def pbox (ir it : ℕ) : Set (ℝ × ℝ) := Ioo (g.rad ir) (g.rad (ir + 1)) ×ˢ Ioo (g.ang it) (g.ang (it + 1))

lemma pbox_subset_target (hNT : 0 < g.NT) {ir it : ℕ} (hit : it < g.NT) :
    g.pbox ir it ⊆ polarCoord.target := by
  intro p hp
  simp only [pbox, mem_prod, mem_Ioo] at hp
  simp only [polarCoord_target, mem_prod, mem_Ioi, mem_Ioo]
  refine ⟨(g.rad_nonneg ir).trans_lt hp.1.1, ?_, ?_⟩
  · have := g.ang_ge hNT it; linarith [hp.2.1, Real.pi_pos]
  · have := g.ang_le hNT (show it + 1 ≤ g.NT by omega); linarith [hp.2.2, Real.pi_pos]

lemma cell_eq (ir it : ℕ) : g.cell ir it = polarCoord.symm '' g.pbox ir it := rfl

lemma isOpen_cell (hNT : 0 < g.NT) {ir it : ℕ} (hit : it < g.NT) : IsOpen (g.cell ir it) :=
  polarCoord.isOpen_image_symm_of_subset_target (isOpen_Ioo.prod isOpen_Ioo) (g.pbox_subset_target hNT hit)

lemma measurableSet_cell (hNT : 0 < g.NT) {ir it : ℕ} (hit : it < g.NT) : MeasurableSet (g.cell ir it) :=
  (g.isOpen_cell hNT hit).measurableSet

lemma cell_subset_Hp (hNT : 0 < g.NT) {ir it : ℕ} (hit : it < g.NT) : g.cell ir it ⊆ Hp := by
  rintro _ ⟨p, hp, rfl⟩
  simp only [mem_prod, mem_Ioo] at hp
  simp only [Hp, mem_ofPred_eq, polarCoord_symm_apply]
  have hr : 0 < p.1 := (g.rad_nonneg ir).trans_lt hp.1.1
  have h1 := g.ang_ge hNT it
  have h2 := g.ang_le hNT (show it + 1 ≤ g.NT by omega)
  have hc : 0 < Real.cos p.2 := Real.cos_pos_of_mem_Ioo ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩
  positivity

lemma cell_norm_le {ir it : ℕ} {z : Pt} (hz : z ∈ g.cell ir it) : |z.1| ≤ g.rad (ir + 1) ∧ |z.2| ≤ g.rad (ir + 1) := by
  obtain ⟨p, hp, rfl⟩ := hz
  simp only [mem_prod, mem_Ioo] at hp
  simp only [polarCoord_symm_apply]
  have hr : 0 < p.1 := (g.rad_nonneg ir).trans_lt hp.1.1
  constructor
  · rw [abs_mul, abs_of_pos hr]
    exact (mul_le_of_le_one_right hr.le (abs_cos_le_one _)).trans hp.1.2.le
  · rw [abs_mul, abs_of_pos hr]
    exact (mul_le_of_le_one_right hr.le (abs_sin_le_one _)).trans hp.1.2.le

lemma volume_cell_ne_top (ir it : ℕ) : volume (g.cell ir it) ≠ ⊤ := by
  have hb : Bornology.IsBounded (g.cell ir it) := by
    refine (Metric.isBounded_closedBall (x := (0 : Pt)) (r := g.rad (ir + 1))).subset fun z hz => ?_
    have := g.cell_norm_le hz
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]
    exact this
  exact hb.measure_lt_top.ne

lemma pbox_disjoint (hNT : 0 < g.NT) {ir it ir' it' : ℕ} (h : (ir, it) ≠ (ir', it')) :
    Disjoint (g.pbox ir it) (g.pbox ir' it') := by
  rw [Set.disjoint_left]
  rintro p hp hp'
  simp only [pbox, mem_prod, mem_Ioo] at hp hp'
  by_cases hr : ir = ir'
  · subst hr
    have hit : it ≠ it' := fun he => h (by rw [he])
    rcases lt_or_gt_of_ne hit with hlt | hlt
    · have := g.ang_mono hNT (show it + 1 ≤ it' by omega); linarith [hp.2.2, hp'.2.1]
    · have := g.ang_mono hNT (show it' + 1 ≤ it by omega); linarith [hp'.2.2, hp.2.1]
  · rcases lt_or_gt_of_ne hr with hlt | hlt
    · have := g.rad_mono (show ir + 1 ≤ ir' by omega); linarith [hp.1.2, hp'.1.1]
    · have := g.rad_mono (show ir' + 1 ≤ ir by omega); linarith [hp'.1.2, hp.1.1]

lemma cell_disjoint (hNT : 0 < g.NT) {ir it ir' it' : ℕ} (hit : it < g.NT) (hit' : it' < g.NT)
    (h : (ir, it) ≠ (ir', it')) : Disjoint (g.cell ir it) (g.cell ir' it') := by
  rw [Set.disjoint_left]
  rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, he⟩
  have hp' : p ∈ polarCoord.symm.source := by rw [polarCoord.symm_source]; exact g.pbox_subset_target hNT hit hp
  have hq' : q ∈ polarCoord.symm.source := by rw [polarCoord.symm_source]; exact g.pbox_subset_target hNT hit' hq
  have hpq : q = p := polarCoord.symm.injOn hq' hp' he
  subst hpq
  exact Set.disjoint_left.1 (g.pbox_disjoint hNT h) hp hq

end GridR

end BHH.W2
