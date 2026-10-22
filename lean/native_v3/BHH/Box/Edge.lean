/-
Module C: boxes with fixed-point corners, laws of the point coordinates under the uniform measure, independence of
edge events (`EdgeIndepProp`), and Prop 3.7 (`StraddleProp`).
-/
import BHH.Box.Indep
import BHH.Box.CdfIv

open MeasureTheory Set Real ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace BHH

open BHH.Cert

/-! ## Boxes with fixed-point corners -/

/-- real lower corner of `boxOf lo hi` -/
def loR (m : ℕ) (lo : List ℤ) : Fin m → ℝ := fun d => fx (lo.getD d.val 0)

lemma boxOf_eq_pi {m : ℕ} (lo hi : List ℤ) :
    (boxOf lo hi : Set (Fin m → ℝ)) = Set.pi univ fun d => Ico (loR m lo d) (loR m hi d) := rfl

lemma validBox_lt {k : ℕ} {lo hi : List ℤ} (hv : ValidBox k lo hi) (d : Fin (mDim k)) :
    loR (mDim k) lo d < loR (mDim k) hi d :=
  fx_lt_iff.2 (hv.2.2.1 d.val d.isLt).1

lemma boxOf_ae_eq_rbox {m : ℕ} (lo hi : List ℤ) :
    (boxOf lo hi : Set (Fin m → ℝ)) =ᵐ[volume] rbox (loR m lo) (loR m hi) := by
  rw [boxOf_eq_pi, rbox, volume_pi, Set.pi_univ_Icc]
  exact Measure.univ_pi_Ico_ae_eq_Icc

lemma measurableSet_boxOf {m : ℕ} (lo hi : List ℤ) : MeasurableSet (boxOf lo hi : Set (Fin m → ℝ)) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

/-- volumes of events in `boxOf` are `vol(box)` times their uniform probability -/
lemma volume_boxOf_inter {m : ℕ} {lo hi : List ℤ} (h : ∀ d, loR m lo d < loR m hi d) (E : Set (Fin m → ℝ)) :
    volume ((boxOf lo hi : Set (Fin m → ℝ)) ∩ E) =
      volume (rbox (loR m lo) (loR m hi)) * unifBox (loR m lo) (loR m hi) E := by
  rw [measure_congr ((boxOf_ae_eq_rbox lo hi).inter (ae_eq_refl E)), Set.inter_comm,
    ← Measure.restrict_apply' measurableSet_rbox, restrict_rbox h, Measure.smul_apply, smul_eq_mul]

lemma volume_boxOf {m : ℕ} {lo hi : List ℤ} (h : ∀ d, loR m lo d < loR m hi d) :
    volume (boxOf lo hi : Set (Fin m → ℝ)) = volume (rbox (loR m lo) (loR m hi)) := by
  have hP := unifBox_isProb h
  have := volume_boxOf_inter h Set.univ
  rwa [Set.inter_univ, measure_univ, mul_one] at this

/-- the integrals over `boxOf` and over the closed box agree -/
lemma setLIntegral_boxOf {m : ℕ} (lo hi : List ℤ) (f : (Fin m → ℝ) → ℝ≥0∞) :
    ∫⁻ x in (boxOf lo hi : Set (Fin m → ℝ)), f x = ∫⁻ x in rbox (loR m lo) (loR m hi), f x :=
  setLIntegral_congr (boxOf_ae_eq_rbox lo hi)

lemma sep_eq_inter {α : Type*} (s : Set α) (p : α → Prop) : {x ∈ s | p x} = s ∩ {x | p x} := rfl

/-! ## Laws of the point coordinates -/

section Laws

variable {m : ℕ} {lo hi : Fin m → ℝ}

lemma oget_le (h : ∀ d, lo d < hi d) (o : Option ℕ) : oget lo o ≤ oget hi o := by
  cases o with
  | none => simp [oget]
  | some n =>
    simp only [oget, xget]
    split_ifs with hn
    · exact (h _).le
    · exact le_rfl

lemma map_oget (h : ∀ d, lo d < hi d) (o : Option ℕ) :
    (unifBox lo hi).map (fun x => oget x o) = uLaw (oget lo o) (oget hi o) := by
  have hP := unifBox_isProb h
  cases o with
  | none => simp [oget, Measure.map_const, uLaw_of_eq]
  | some n =>
    simp only [oget, xget]
    split_ifs with hn
    · rw [uLaw_of_lt (h _)]; exact unifBox_map_eval h _
    · simp [Measure.map_const, uLaw_of_eq]

lemma map_oget_pair (h : ∀ d, lo d < hi d) {o₁ o₂ : Option ℕ} (ho : ∀ d, o₁ = some d → o₂ ≠ some d) :
    (unifBox lo hi).map (fun x => (oget x o₁, oget x o₂)) =
      (uLaw (oget lo o₁) (oget hi o₁)).prod (uLaw (oget lo o₂) (oget hi o₂)) := by
  have hP := unifBox_isProb h
  have hind := indepFun_of_depOn h (osupp_disjoint ho) (measurable_oget o₁) (measurable_oget o₂)
    (depOn_oget o₁) (depOn_oget o₂)
  rw [hind.map_prod_eq_prod_map_map (measurable_oget o₁).aemeasurable (measurable_oget o₂).aemeasurable,
    map_oget h, map_oget h]

lemma measurable_oget_pair (o₁ o₂ : Option ℕ) :
    Measurable fun x : Fin m → ℝ => (oget x o₁, oget x o₂) :=
  (measurable_oget o₁).prodMk (measurable_oget o₂)

/-- `P(X_{o₁} - X_{o₂} ≤ z) = cdfR(...)` -/
lemma unifBox_sub_le (h : ∀ d, lo d < hi d) {o₁ o₂ : Option ℕ} (ho : ∀ d, o₁ = some d → o₂ ≠ some d)
    (z : ℝ) :
    unifBox lo hi {x | oget x o₁ - oget x o₂ ≤ z} =
      ENNReal.ofReal (cdfR (oget lo o₁) (oget hi o₁) (oget lo o₂) (oget hi o₂) z) := by
  have e : {x : Fin m → ℝ | oget x o₁ - oget x o₂ ≤ z} =
      (fun x => (oget x o₁, oget x o₂)) ⁻¹' {p : ℝ × ℝ | p.1 - p.2 ≤ z} := rfl
  rw [e, ← Measure.map_apply (measurable_oget_pair o₁ o₂) (measurableSet_sub_le z), map_oget_pair h ho,
    cdf_prod (oget_le h o₁) (oget_le h o₂)]

/-- no atoms for `X_{o₁} - X_{o₂}` if one of the two coordinates is not constant -/
lemma unifBox_sub_eq (h : ∀ d, lo d < hi d) {o₁ o₂ : Option ℕ} (ho : ∀ d, o₁ = some d → o₂ ≠ some d)
    (hnd : oget lo o₁ < oget hi o₁ ∨ oget lo o₂ < oget hi o₂) (z : ℝ) :
    unifBox lo hi {x | oget x o₁ - oget x o₂ = z} = 0 := by
  have e : {x : Fin m → ℝ | oget x o₁ - oget x o₂ = z} =
      (fun x => (oget x o₁, oget x o₂)) ⁻¹' {p : ℝ × ℝ | p.1 - p.2 = z} := rfl
  have hm : MeasurableSet {p : ℝ × ℝ | p.1 - p.2 = z} :=
    measurableSet_eq_fun (measurable_fst.sub measurable_snd) measurable_const
  rw [e, ← Measure.map_apply (measurable_oget_pair o₁ o₂) hm, map_oget_pair h ho]
  exact prod_sub_eq_null hnd z

end Laws

/-! ## Edge events -/

section EdgeEv

variable {k : ℕ}

lemma continuous_xcfg (j : Fin k) : Continuous fun x : Fin (mDim k) → ℝ => xcfg k x j := by
  have : (fun x : Fin (mDim k) → ℝ => xcfg k x j) = fun x => (oget x (pc1 j.val), oget x (pc2 j.val)) :=
    funext fun x => xcfg_eq k x j
  rw [this]; exact (continuous_oget _).prodMk (continuous_oget _)

/-- the squared distance of the points `i`, `j` as a function of `x` -/
def pairSq (k : ℕ) (i j : Fin k) (x : Fin (mDim k) → ℝ) : ℝ := sqDist (xcfg k x i) (xcfg k x j)

lemma continuous_pairSq (i j : Fin k) : Continuous (pairSq k i j) := by
  unfold pairSq sqDist
  have hi := continuous_xcfg (k := k) i
  have hj := continuous_xcfg (k := k) j
  fun_prop

lemma depOn_pairSq (i j : Fin k) : DepOn (ptSupp k i.val ∪ ptSupp k j.val) (pairSq k i j) := by
  intro x x' hx
  have h1 : xcfg k x i = xcfg k x' i := depOn_xcfg k i x x' fun d hd => hx d (Finset.mem_union_left _ hd)
  have h2 : xcfg k x j = xcfg k x' j := depOn_xcfg k j x x' fun d hd => hx d (Finset.mem_union_right _ hd)
  show sqDist (xcfg k x i) (xcfg k x j) = sqDist (xcfg k x' i) (xcfg k x' j)
  rw [h1, h2]

theorem edgeIndepProp : EdgeIndepProp := by
  intro k lo hi hv i₁ j₁ i₂ j₂ h1 h2 h3 h4 S₁ S₂ hS₁ hS₂
  have h := validBox_lt hv
  set L := loR (mDim k) lo
  set H := loR (mDim k) hi
  have hdisj : Disjoint (ptSupp k i₁.val ∪ ptSupp k j₁.val) (ptSupp k i₂.val ∪ ptSupp k j₂.val) := by
    rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
    exact ⟨⟨ptSupp_disjoint k (Fin.val_injective.ne h1), ptSupp_disjoint k (Fin.val_injective.ne h2)⟩,
      ⟨ptSupp_disjoint k (Fin.val_injective.ne h3), ptSupp_disjoint k (Fin.val_injective.ne h4)⟩⟩
  have hind := indepFun_of_depOn h hdisj (continuous_pairSq i₁ j₁).measurable
    (continuous_pairSq i₂ j₂).measurable (depOn_pairSq i₁ j₁) (depOn_pairSq i₂ j₂)
  have hmeas := hind.measure_inter_preimage_eq_mul S₁ S₂ hS₁ hS₂
  have m1 : MeasurableSet (pairSq k i₁ j₁ ⁻¹' S₁) := (continuous_pairSq i₁ j₁).measurable hS₁
  have m2 : MeasurableSet (pairSq k i₂ j₂ ⁻¹' S₂) := (continuous_pairSq i₂ j₂).measurable hS₂
  have e12 : {x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)) |
      sqDist (xcfg k x i₁) (xcfg k x j₁) ∈ S₁ ∧ sqDist (xcfg k x i₂) (xcfg k x j₂) ∈ S₂} =
      boxOf lo hi ∩ (pairSq k i₁ j₁ ⁻¹' S₁ ∩ pairSq k i₂ j₂ ⁻¹' S₂) := rfl
  have e1 : {x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)) | sqDist (xcfg k x i₁) (xcfg k x j₁) ∈ S₁} =
      boxOf lo hi ∩ pairSq k i₁ j₁ ⁻¹' S₁ := rfl
  have e2 : {x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)) | sqDist (xcfg k x i₂) (xcfg k x j₂) ∈ S₂} =
      boxOf lo hi ∩ pairSq k i₂ j₂ ⁻¹' S₂ := rfl
  rw [e12, e1, e2, volume_boxOf_inter h, volume_boxOf_inter h, volume_boxOf_inter h,
    volume_boxOf h, hmeas]
  ring

/-- Frechet: `vol(F₁ ∩ F₂) ≥ vol F₁ + vol F₂ - vol Q` -/
lemma frechet {α : Type*} [MeasurableSpace α] {μ : Measure α} {Q F₁ F₂ : Set α} (h1 : F₁ ⊆ Q) (h2 : F₂ ⊆ Q)
    (hm : MeasurableSet F₂) : μ F₁ + μ F₂ ≤ μ (F₁ ∩ F₂) + μ Q := by
  rw [← measure_union_add_inter₀ F₁ hm.nullMeasurableSet, add_comm (μ (F₁ ∪ F₂))]
  exact add_le_add le_rfl (measure_mono (Set.union_subset h1 h2))

/-- the product form of independence used by the leaf -/
lemma volume_inter_ge_of_indep {α : Type*} [MeasurableSpace α] {μ : Measure α} {Q F₁ F₂ : Set α}
    {q₁ q₂ : ℝ} (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) (hQ : μ Q ≠ ⊤)
    (hind : μ (F₁ ∩ F₂) * μ Q = μ F₁ * μ F₂)
    (h1 : ENNReal.ofReal (q₁ * (μ Q).toReal) ≤ μ F₁) (h2 : ENNReal.ofReal (q₂ * (μ Q).toReal) ≤ μ F₂) :
    ENNReal.ofReal (q₁ * q₂ * (μ Q).toReal) ≤ μ (F₁ ∩ F₂) := by
  rcases eq_or_ne (μ Q) 0 with h0 | h0
  · rw [h0, ENNReal.toReal_zero, mul_zero, ENNReal.ofReal_zero]; exact zero_le
  have hQ' : μ Q = ENNReal.ofReal (μ Q).toReal := (ENNReal.ofReal_toReal hQ).symm
  have hv : 0 < (μ Q).toReal := ENNReal.toReal_pos h0 hQ
  have key : ENNReal.ofReal (q₁ * q₂ * (μ Q).toReal) * μ Q ≤ μ (F₁ ∩ F₂) * μ Q := by
    rw [hind]
    calc ENNReal.ofReal (q₁ * q₂ * (μ Q).toReal) * μ Q
        = ENNReal.ofReal (q₁ * (μ Q).toReal) * ENNReal.ofReal (q₂ * (μ Q).toReal) := by
          rw [hQ', ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ENNReal.toReal_ofReal hv.le]
          ring_nf
      _ ≤ μ F₁ * μ F₂ := mul_le_mul' h1 h2
  exact (ENNReal.mul_le_mul_iff_left h0 hQ).1 key

end EdgeEv

/-! ## Prop 3.7 -/

lemma mem_boxOf_iffC {m : ℕ} {lo hi : List ℤ} {x : Fin m → ℝ} :
    x ∈ (boxOf lo hi : Set (Fin m → ℝ)) ↔ ∀ d, loR m lo d ≤ x d ∧ x d < loR m hi d := by
  rw [boxOf_eq_pi]; simp only [Set.mem_univ_pi, Set.mem_Ico]

lemma xget_of_ltC {m : ℕ} (x : Fin m → ℝ) {n : ℕ} (h : n < m) : xget x n = x ⟨n, h⟩ := by
  simp [xget, h]

lemma oget_some_of_lt {m : ℕ} (x : Fin m → ℝ) {n : ℕ} (h : n < m) : oget x (some n) = x ⟨n, h⟩ :=
  xget_of_ltC x h

theorem straddleProp : StraddleProp := by
  intro k lo hi j hv hj2 hjk hlo0 hlo2 hord
  have h := validBox_lt hv
  have hm : mDim k = 2 * k - 3 := rfl
  have hd1 : 2 * j - 3 < mDim k := by omega
  have hd2 : 2 * (j + 1) - 3 < mDim k := by omega
  set L := loR (mDim k) lo
  set H := loR (mDim k) hi
  constructor
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hx, hD⟩
      exact ⟨hx, hD.2.2 j hj2 hjk⟩
    · rintro ⟨hx, hxj⟩
      refine ⟨hx, ?_, ?_, ?_⟩
      · rw [xget_of_ltC x (by omega : 0 < mDim k)]
        exact (fx_nonneg_iff.2 hlo0).trans ((mem_boxOf_iffC.1 hx) ⟨0, by omega⟩).1
      · rw [xget_of_ltC x (by omega : 2 < mDim k)]
        exact (fx_nonneg_iff.2 (hlo2 (by omega))).trans ((mem_boxOf_iffC.1 hx) ⟨2, by omega⟩).1
      · intro j' hj'2 hj'k
        by_cases hjj : j' = j
        · subst hjj; exact hxj
        · have ha : 2 * j' - 3 < mDim k := by omega
          have hb : 2 * (j' + 1) - 3 < mDim k := by omega
          rw [xget_of_ltC x ha, xget_of_ltC x hb]
          have h1 := ((mem_boxOf_iffC.1 hx) ⟨2 * j' - 3, ha⟩).2
          have h2 := ((mem_boxOf_iffC.1 hx) ⟨2 * (j' + 1) - 3, hb⟩).1
          have h3 : H ⟨2 * j' - 3, ha⟩ ≤ L ⟨2 * (j' + 1) - 3, hb⟩ := fx_le_iff.2 (hord j' hj'2 hj'k hjj)
          linarith
  · -- the volume
    have hdd : ∀ d, some (2 * j - 3) = some d → some (2 * (j + 1) - 3) ≠ some d := by
      intro d h1 h2; simp only [Option.some.injEq] at h1 h2; omega
    have e : {x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)) | xget x (2 * j - 3) ≤ xget x (2 * (j + 1) - 3)} =
        boxOf lo hi ∩ {x | oget x (some (2 * j - 3)) - oget x (some (2 * (j + 1) - 3)) ≤ 0} := by
      ext x; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, oget, sub_nonpos]
    rw [e, volume_boxOf_inter h, unifBox_sub_le h hdd 0]
    rw [oget_some_of_lt L hd1, oget_some_of_lt H hd1, oget_some_of_lt L hd2, oget_some_of_lt H hd2]
    have hlh1 := (hv.2.2.1 _ hd1).1
    have hlh2 := (hv.2.2.1 _ hd2).1
    have hc := ivMem_lo_le (cdfIvProp _ _ _ _ 0 hlh1.le hlh2.le)
    rw [fx_zeroC] at hc
    have hVt : volume (rbox L H) ≠ ⊤ := volume_rbox_ne_top
    rw [volume_boxOf h]
    refine (ENNReal.ofReal_le_ofReal (q := (volume (rbox L H)).toReal *
      cdfR (L ⟨_, hd1⟩) (H ⟨_, hd1⟩) (L ⟨_, hd2⟩) (H ⟨_, hd2⟩) 0) ?_).trans (le_of_eq ?_)
    · rw [mul_comm]; exact mul_le_mul_of_nonneg_left hc ENNReal.toReal_nonneg
    · rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hVt]

end BHH
