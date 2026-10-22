/-
Module C: Lemma 3.3 and the bounds for the vertex remainder `ϱ = vertexRemSeg` on a box
(`PointDispProp`, `RemMaxProp`, `RemMomentsProp`).
-/
import BHH.Box.Indep
import BHH.Box.Bracket
import BHH.Box.Disks

open MeasureTheory Set Real ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace BHH

/-! ## The function `T` -/

lemma Tseg_eq (dlo dhi : ℝ) (first : Bool) (w : ℝ) :
    Tseg dlo dhi first w = lamT dhi first * w + muT dlo dhi first + min (w / dlo) π := by
  unfold Tseg lamT muT
  cases first <;> simp [div_eq_mul_one_div w]
  ring

lemma lamT_nonneg (dhi : ℝ) (first : Bool) : 0 ≤ lamT dhi first := by
  unfold lamT; split_ifs
  · exact one_div_nonneg.2 (Real.sqrt_nonneg _)
  · exact le_rfl

lemma muT_nonneg {dlo dhi : ℝ} (first : Bool) (hle : dlo ≤ dhi) (h2 : dlo < 2) :
    0 ≤ muT dlo dhi first := by
  unfold muT; split_ifs
  · exact le_rfl
  · have : Real.arcsin (dlo / 2) ≤ Real.arcsin (min dhi 2 / 2) :=
      Real.arcsin_le_arcsin (by have := le_min hle h2.le; linarith)
    linarith

lemma Tseg_nonneg {dlo dhi : ℝ} (first : Bool) (hdl : 0 < dlo) (hle : dlo ≤ dhi) (h2 : dlo < 2)
    {w : ℝ} (hw : 0 ≤ w) : 0 ≤ Tseg dlo dhi first w := by
  rw [Tseg_eq]
  have := lamT_nonneg dhi first
  have := muT_nonneg first hle h2
  have : 0 ≤ min (w / dlo) π := le_min (div_nonneg hw hdl.le) Real.pi_pos.le
  positivity

lemma Tseg_mono {dlo dhi : ℝ} (first : Bool) (hdl : 0 < dlo) {w w' : ℝ} (hww : w ≤ w') :
    Tseg dlo dhi first w ≤ Tseg dlo dhi first w' := by
  rw [Tseg_eq, Tseg_eq]
  have h1 := mul_le_mul_of_nonneg_left hww (lamT_nonneg dhi first)
  have h2 : min (w / dlo) π ≤ min (w' / dlo) π :=
    min_le_min (div_le_div_of_nonneg_right hww hdl.le) le_rfl
  linarith

lemma continuous_Tseg (dlo dhi : ℝ) (first : Bool) : Continuous (Tseg dlo dhi first) := by
  have : Tseg dlo dhi first = fun w => lamT dhi first * w + muT dlo dhi first + min (w / dlo) π :=
    funext (Tseg_eq dlo dhi first)
  rw [this]; fun_prop

/-- `χ T(χ) = λχ² + μχ + min(χ²/d⁻, πχ)` -/
lemma mul_Tseg {dlo dhi : ℝ} (first : Bool) {χ : ℝ} (hχ : 0 ≤ χ) :
    χ * Tseg dlo dhi first χ =
      lamT dhi first * χ ^ 2 + muT dlo dhi first * χ + min (χ ^ 2 / dlo) (π * χ) := by
  rw [Tseg_eq, mul_add, mul_add, mul_min_of_nonneg _ _ hχ]
  have e1 : χ * (χ / dlo) = χ ^ 2 / dlo := by ring
  rw [e1, mul_comm χ π]
  ring

/-! ## `RemMaxProp` -/

lemma enorm2_nonneg (a : Pt) : 0 ≤ enorm2 a := Real.sqrt_nonneg _

lemma enorm2_eq_edist2 (a b : Pt) : enorm2 (a - b) = edist2 a b := rfl

lemma enorm2_sub_le (a b : Pt) : enorm2 (a - b) ≤ enorm2 a + enorm2 b := by
  have h := edist2_triangle a 0 b
  have e1 : edist2 a 0 = enorm2 a := by simp [edist2, enorm2, sqDist]
  have e2 : edist2 0 b = enorm2 b := by simp [edist2, enorm2, sqDist]
  rw [enorm2_eq_edist2]; linarith

theorem remMaxProp : RemMaxProp := by
  intro k c y eps dlo dhi first hd hy
  unfold vertexRemSeg
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  split_ifs with hij
  · obtain ⟨hdl, hle⟩ := hd i j hij.1 hij.2
    have hν : (0 : ℝ) ≤ (nuCountSeg c eps dlo dhi first i j : ℝ) := Nat.cast_nonneg _
    have hw : enorm2 ((y j - c j) - (y i - c i)) ≤ eps i + eps j :=
      (enorm2_sub_le _ _).trans (by linarith [hy i, hy j])
    have hT := Tseg_mono (dhi := dhi i j) (first i j) hdl hw
    have hT0 := Tseg_nonneg (first i j) hdl hle hij.2 (enorm2_nonneg ((y j - c j) - (y i - c i)))
    have hs : enorm2 (y i - c i) + enorm2 (y j - c j) ≤ eps i + eps j := add_le_add (hy i) (hy j)
    have hs0 : 0 ≤ enorm2 (y i - c i) + enorm2 (y j - c j) :=
      add_nonneg (enorm2_nonneg _) (enorm2_nonneg _)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hs hν) hT hT0 (mul_nonneg hν (hs0.trans hs))
  · exact le_rfl

/-! ## Displacements of the points on a box -/

section Disp

variable {k : ℕ} {lo hi : Fin (mDim k) → ℝ}

/-- the centre configuration of the box -/
def cfgC (k : ℕ) (lo hi : Fin (mDim k) → ℝ) : Fin k → Pt := xcfg k (fun d => (lo d + hi d) / 2)

/-- `|δ_j| = |y_j - c_j|` as a function of `x` -/
def rpt (k : ℕ) (lo hi : Fin (mDim k) → ℝ) (j : Fin k) (x : Fin (mDim k) → ℝ) : ℝ :=
  enorm2 (xcfg k x j - cfgC k lo hi j)

lemma sub_cfgC (j : Fin k) (x : Fin (mDim k) → ℝ) :
    xcfg k x j - cfgC k lo hi j = (ucen lo hi (pc1 j.val) x, ucen lo hi (pc2 j.val) x) := by
  unfold cfgC ucen
  rw [xcfg_eq, xcfg_eq]
  rfl

lemma rpt_eq (j : Fin k) (x : Fin (mDim k) → ℝ) :
    rpt k lo hi j x = √(ucen lo hi (pc1 j.val) x ^ 2 + ucen lo hi (pc2 j.val) x ^ 2) := by
  unfold rpt enorm2; rw [sub_cfgC]

lemma rpt_nonneg (j : Fin k) (x : Fin (mDim k) → ℝ) : 0 ≤ rpt k lo hi j x := Real.sqrt_nonneg _

lemma rpt_sq (j : Fin k) (x : Fin (mDim k) → ℝ) :
    rpt k lo hi j x ^ 2 = ucen lo hi (pc1 j.val) x ^ 2 + ucen lo hi (pc2 j.val) x ^ 2 := by
  rw [rpt_eq]; exact Real.sq_sqrt (by positivity)

/-- the half-diagonal of the rectangle of the point `j` -/
def hdiag (k : ℕ) (lo hi : Fin (mDim k) → ℝ) (j : Fin k) : ℝ :=
  √((halfSides k lo hi j).1 ^ 2 + (halfSides k lo hi j).2 ^ 2)

lemma rpt_le {x : Fin (mDim k) → ℝ} (hx : x ∈ rbox lo hi) (j : Fin k) : rpt k lo hi j x ≤ hdiag k lo hi j := by
  rw [rpt_eq, hdiag, halfSides_eqC]
  apply Real.sqrt_le_sqrt
  have h1 := abs_ucen_le hx (pc1 j.val)
  have h2 := abs_ucen_le hx (pc2 j.val)
  have h1' := sq_le_sq' (abs_le.1 h1).1 (abs_le.1 h1).2
  have h2' := sq_le_sq' (abs_le.1 h2).1 (abs_le.1 h2).2
  simp only
  linarith

lemma hdiag_nonneg (j : Fin k) : 0 ≤ hdiag k lo hi j := Real.sqrt_nonneg _

lemma continuous_ucen (o : Option ℕ) : Continuous (ucen lo hi o) :=
  (continuous_oget o).sub continuous_const

lemma continuous_rpt (j : Fin k) : Continuous (rpt k lo hi j) := by
  have : rpt k lo hi j = fun x => √(ucen lo hi (pc1 j.val) x ^ 2 + ucen lo hi (pc2 j.val) x ^ 2) :=
    funext (rpt_eq j)
  rw [this]
  exact ((continuous_ucen _).pow 2 |>.add ((continuous_ucen _).pow 2)).sqrt

lemma depOn_rpt (j : Fin k) : DepOn (ptSupp k j.val) (rpt k lo hi j) := by
  intro x x' hx
  have h1 : xcfg k x j = xcfg k x' j := depOn_xcfg k j x x' hx
  show enorm2 (xcfg k x j - cfgC k lo hi j) = enorm2 (xcfg k x' j - cfgC k lo hi j)
  rw [h1]

lemma depOn_ucen_pt (j : Fin k) (b : Bool) :
    DepOn (ptSupp k j.val) (ucen lo hi (if b then pc1 j.val else pc2 j.val)) := by
  cases b
  · exact (depOn_ucen lo hi _).mono Finset.subset_union_right
  · exact (depOn_ucen lo hi _).mono Finset.subset_union_left

end Disp

theorem pointDispProp : PointDispProp := by
  intro k lo hi _ x hx j
  exact rpt_le hx j

/-! ## Moments of the displacements -/

section MomentsPt

variable {k : ℕ} {lo hi : Fin (mDim k) → ℝ}

lemma int_rpt_pow (h : ∀ d, lo d < hi d) (j : Fin k) (n : ℕ) :
    Integrable (fun x => rpt k lo hi j x ^ n) (unifBox lo hi) :=
  int_of_bdd h ((continuous_rpt j).pow n).measurable.aestronglyMeasurable (hdiag k lo hi j ^ n)
    fun x hx => by
      rw [abs_pow, abs_of_nonneg (rpt_nonneg j x)]
      exact pow_le_pow_left₀ (rpt_nonneg j x) (rpt_le hx j) n

lemma int_ucen_pow (h : ∀ d, lo d < hi d) (o : Option ℕ) (n : ℕ) :
    Integrable (fun x => ucen lo hi o x ^ n) (unifBox lo hi) :=
  int_of_bdd h ((measurable_ucen lo hi o).pow_const n).aestronglyMeasurable (ohalf lo hi o ^ n)
    fun x hx => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_ucen_le hx o) n

lemma integral_rpt_sq (h : ∀ d, lo d < hi d) (j : Fin k) :
    ∫ x, rpt k lo hi j x ^ 2 ∂unifBox lo hi = m2pt (halfSides k lo hi j) := by
  simp_rw [rpt_sq]
  rw [integral_add (int_ucen_pow h _ 2) (int_ucen_pow h _ 2), integral_ucen_sq h, integral_ucen_sq h,
    halfSides_eqC, m2pt]
  ring

lemma integral_rpt_four (h : ∀ d, lo d < hi d) (j : Fin k) :
    ∫ x, rpt k lo hi j x ^ 4 ∂unifBox lo hi = m4pt (halfSides k lo hi j) := by
  have e : ∀ x, rpt k lo hi j x ^ 4 = ucen lo hi (pc1 j.val) x ^ 4 +
      2 * (ucen lo hi (pc1 j.val) x ^ 2 * ucen lo hi (pc2 j.val) x ^ 2) + ucen lo hi (pc2 j.val) x ^ 4 := by
    intro x
    have := rpt_sq (lo := lo) (hi := hi) j x
    calc rpt k lo hi j x ^ 4 = (rpt k lo hi j x ^ 2) ^ 2 := by ring
      _ = _ := by rw [this]; ring
  simp_rw [e]
  have i12 : Integrable (fun x => ucen lo hi (pc1 j.val) x ^ 2 * ucen lo hi (pc2 j.val) x ^ 2)
      (unifBox lo hi) :=
    int_of_bdd h (((measurable_ucen lo hi _).pow_const 2).mul ((measurable_ucen lo hi _).pow_const 2)).aestronglyMeasurable
      (ohalf lo hi (pc1 j.val) ^ 2 * ohalf lo hi (pc2 j.val) ^ 2) fun x hx => by
        rw [abs_mul, abs_pow, abs_pow]
        exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (abs_ucen_le hx _) 2)
          (pow_le_pow_left₀ (abs_nonneg _) (abs_ucen_le hx _) 2) (by positivity) (by positivity)
  have i1 : Integrable (fun x => ucen lo hi (pc1 j.val) x ^ 4 +
      2 * (ucen lo hi (pc1 j.val) x ^ 2 * ucen lo hi (pc2 j.val) x ^ 2)) (unifBox lo hi) :=
    (int_ucen_pow h _ 4).add (i12.const_mul 2)
  rw [integral_add i1 (int_ucen_pow h _ 4), integral_add (int_ucen_pow h _ 4) (i12.const_mul 2),
    integral_const_mul]
  have hind : ∫ x, ucen lo hi (pc1 j.val) x ^ 2 * ucen lo hi (pc2 j.val) x ^ 2 ∂unifBox lo hi =
      (∫ x, ucen lo hi (pc1 j.val) x ^ 2 ∂unifBox lo hi) * ∫ x, ucen lo hi (pc2 j.val) x ^ 2 ∂unifBox lo hi :=
    integral_mul_of_depOn h (osupp_disjoint (pc12_disjoint j.val))
      ((measurable_ucen lo hi _).pow_const 2) ((measurable_ucen lo hi _).pow_const 2)
      ((depOn_ucen lo hi _).comp (fun t => t ^ 2)) ((depOn_ucen lo hi _).comp (fun t => t ^ 2))
  rw [hind, integral_ucen_four h, integral_ucen_four h, integral_ucen_sq h, integral_ucen_sq h,
    halfSides_eqC, m4pt]
  ring

lemma integral_rpt_le (h : ∀ d, lo d < hi d) (j : Fin k) :
    ∫ x, rpt k lo hi j x ∂unifBox lo hi ≤ √(m2pt (halfSides k lo hi j)) := by
  have hP := unifBox_isProb h
  have hcs := integral_mul_sq_le (μ := unifBox lo hi) (U := rpt k lo hi j) (V := fun _ => (1 : ℝ))
    (int_rpt_pow h j 2) (by simp) (by simpa using int_rpt_pow h j 1)
  simp only [mul_one, one_pow, integral_const, smul_eq_mul] at hcs
  rw [← integral_rpt_sq h j]
  exact (le_abs_self _).trans (Real.abs_le_sqrt (by simpa using hcs))

lemma integral_rpt_nonneg (j : Fin k) :
    0 ≤ ∫ x, rpt k lo hi j x ∂unifBox lo hi :=
  integral_nonneg fun x => rpt_nonneg j x

lemma integral_rpt_mul (h : ∀ d, lo d < hi d) {i j : Fin k} (hij : i ≠ j) :
    ∫ x, rpt k lo hi i x * rpt k lo hi j x ∂unifBox lo hi =
      (∫ x, rpt k lo hi i x ∂unifBox lo hi) * ∫ x, rpt k lo hi j x ∂unifBox lo hi :=
  integral_mul_of_depOn h (ptSupp_disjoint k (Fin.val_injective.ne hij)) (continuous_rpt i).measurable
    (continuous_rpt j).measurable (depOn_rpt i) (depOn_rpt j)

/-- `Eχ`, `Eχ²`, `Eχ⁴` for `χ = |δ_i| + |δ_j|`, `i ≠ j` -/
lemma chi_moments (h : ∀ d, lo d < hi d) {i j : Fin k} (hij : i ≠ j) :
    let m2 := fun j => m2pt (halfSides k lo hi j)
    let m4 := fun j => m4pt (halfSides k lo hi j)
    ∫ x, (rpt k lo hi i x + rpt k lo hi j x) ∂unifBox lo hi ≤ √(m2 i) + √(m2 j) ∧
    ∫ x, (rpt k lo hi i x + rpt k lo hi j x) ^ 2 ∂unifBox lo hi ≤
      m2 i + m2 j + 2 * √(m2 i) * √(m2 j) ∧
    ∫ x, (rpt k lo hi i x + rpt k lo hi j x) ^ 4 ∂unifBox lo hi ≤ 8 * (m4 i + m4 j) := by
  intro m2 m4
  have hP := unifBox_isProb h
  have ii := int_rpt_pow h i 1
  have ij := int_rpt_pow h j 1
  simp only [pow_one] at ii ij
  refine ⟨?_, ?_, ?_⟩
  · rw [integral_add ii ij]
    exact add_le_add (integral_rpt_le h i) (integral_rpt_le h j)
  · have imul : Integrable (fun x => rpt k lo hi i x * rpt k lo hi j x) (unifBox lo hi) :=
      int_of_bdd h ((continuous_rpt i).mul (continuous_rpt j)).measurable.aestronglyMeasurable
        (hdiag k lo hi i * hdiag k lo hi j) fun x hx => by
          rw [abs_mul, abs_of_nonneg (rpt_nonneg i x), abs_of_nonneg (rpt_nonneg j x)]
          exact mul_le_mul (rpt_le hx i) (rpt_le hx j) (rpt_nonneg j x) (hdiag_nonneg i)
    have e : ∀ x, (rpt k lo hi i x + rpt k lo hi j x) ^ 2 =
        rpt k lo hi i x ^ 2 + 2 * (rpt k lo hi i x * rpt k lo hi j x) + rpt k lo hi j x ^ 2 :=
      fun x => by ring
    simp_rw [e]
    have i1 : Integrable (fun x => rpt k lo hi i x ^ 2 + 2 * (rpt k lo hi i x * rpt k lo hi j x))
        (unifBox lo hi) := (int_rpt_pow h i 2).add (imul.const_mul 2)
    rw [integral_add i1 (int_rpt_pow h j 2), integral_add (int_rpt_pow h i 2) (imul.const_mul 2),
      integral_const_mul, integral_rpt_mul h hij, integral_rpt_sq h i, integral_rpt_sq h j]
    have h1 := integral_rpt_le h i
    have h2 := integral_rpt_le h j
    have h3 := integral_rpt_nonneg (lo := lo) (hi := hi) i
    have h4 := integral_rpt_nonneg (lo := lo) (hi := hi) j
    have : (∫ x, rpt k lo hi i x ∂unifBox lo hi) * ∫ x, rpt k lo hi j x ∂unifBox lo hi ≤
        √(m2 i) * √(m2 j) := mul_le_mul h1 h2 h4 (Real.sqrt_nonneg _)
    simp only [m2] at this ⊢
    linarith
  · have hpt : ∀ x, (rpt k lo hi i x + rpt k lo hi j x) ^ 4 ≤
        8 * (rpt k lo hi i x ^ 4 + rpt k lo hi j x ^ 4) := fun x => by
      nlinarith [sq_nonneg (rpt k lo hi i x - rpt k lo hi j x), sq_nonneg (rpt k lo hi i x + rpt k lo hi j x),
        sq_nonneg (rpt k lo hi i x ^ 2 - rpt k lo hi j x ^ 2), rpt_nonneg (lo := lo) (hi := hi) i x,
        rpt_nonneg (lo := lo) (hi := hi) j x, mul_nonneg (rpt_nonneg (lo := lo) (hi := hi) i x)
        (rpt_nonneg (lo := lo) (hi := hi) j x)]
    have i4 : Integrable (fun x => (rpt k lo hi i x + rpt k lo hi j x) ^ 4) (unifBox lo hi) :=
      int_of_bdd h (((continuous_rpt i).add (continuous_rpt j)).pow 4).measurable.aestronglyMeasurable
        ((hdiag k lo hi i + hdiag k lo hi j) ^ 4) fun x hx => by
          rw [abs_pow, abs_of_nonneg (add_nonneg (rpt_nonneg i x) (rpt_nonneg j x))]
          exact pow_le_pow_left₀ (add_nonneg (rpt_nonneg i x) (rpt_nonneg j x))
            (add_le_add (rpt_le hx i) (rpt_le hx j)) 4
    calc ∫ x, (rpt k lo hi i x + rpt k lo hi j x) ^ 4 ∂unifBox lo hi
        ≤ ∫ x, 8 * (rpt k lo hi i x ^ 4 + rpt k lo hi j x ^ 4) ∂unifBox lo hi :=
          integral_mono i4 (((int_rpt_pow h i 4).add (int_rpt_pow h j 4)).const_mul 8) hpt
      _ = 8 * (m4 i + m4 j) := by
          rw [integral_const_mul, integral_add (int_rpt_pow h i 4) (int_rpt_pow h j 4),
            integral_rpt_four h i, integral_rpt_four h j]

end MomentsPt

/-! ## Minkowski for finite sums -/

lemma integral_sum_sq_le {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (S : Finset ι)
    (t : ι → Ω → ℝ) (hint : ∀ p q, Integrable (fun x => t p x * t q x) μ) :
    ∫ x, (∑ p ∈ S, t p x) ^ 2 ∂μ ≤ (∑ p ∈ S, √(∫ x, t p x ^ 2 ∂μ)) ^ 2 := by
  have e : ∀ x, (∑ p ∈ S, t p x) ^ 2 = ∑ p ∈ S, ∑ q ∈ S, t p x * t q x := fun x => by
    rw [sq, Finset.sum_mul_sum]
  simp_rw [e]
  rw [integral_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => hint p q]
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [integral_finsetSum _ fun q _ => hint p q]
  refine Finset.sum_le_sum fun q _ => ?_
  have hp : Integrable (fun x => t p x ^ 2) μ := by simpa [sq] using hint p p
  have hq : Integrable (fun x => t q x ^ 2) μ := by simpa [sq] using hint q q
  have hA : 0 ≤ ∫ x, t p x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  rw [← Real.sqrt_mul hA]
  exact (le_abs_self _).trans (Real.abs_le_sqrt (integral_mul_sq_le hp hq (hint p q)))

/-! ## One term of the vertex remainder -/

section Pair

variable {k : ℕ} {lo hi : Fin (mDim k) → ℝ}

/-- the term of the pair `ij` of `ϱ`, without the factor `ν` -/
def remTerm (k : ℕ) (lo hi : Fin (mDim k) → ℝ) (i j : Fin k) (dl dh : ℝ) (fst : Bool)
    (x : Fin (mDim k) → ℝ) : ℝ :=
  (rpt k lo hi i x + rpt k lo hi j x) *
    Tseg dl dh fst (enorm2 ((xcfg k x j - cfgC k lo hi j) - (xcfg k x i - cfgC k lo hi i)))

/-- `B(χ) = λχ² + μχ + min(χ²/d⁻, πχ)` -/
def Bfun (dl dh : ℝ) (fst : Bool) (χ : ℝ) : ℝ :=
  lamT dh fst * χ ^ 2 + muT dl dh fst * χ + min (χ ^ 2 / dl) (π * χ)

lemma continuous_remTerm (i j : Fin k) (dl dh : ℝ) (fst : Bool) :
    Continuous (remTerm k lo hi i j dl dh fst) := by
  unfold remTerm
  refine ((continuous_rpt i).add (continuous_rpt j)).mul ((continuous_Tseg dl dh fst).comp ?_)
  have hc : ∀ l : Fin k, Continuous fun x : Fin (mDim k) → ℝ => xcfg k x l := by
    intro l
    have : (fun x : Fin (mDim k) → ℝ => xcfg k x l) =
        fun x => (oget x (pc1 l.val), oget x (pc2 l.val)) := funext fun x => xcfg_eq k x l
    rw [this]; exact (continuous_oget _).prodMk (continuous_oget _)
  unfold enorm2
  fun_prop

lemma remTerm_nonneg {i j : Fin k} {dl dh : ℝ} (fst : Bool) (hdl : 0 < dl) (hle : dl ≤ dh) (h2 : dl < 2)
    (x : Fin (mDim k) → ℝ) : 0 ≤ remTerm k lo hi i j dl dh fst x :=
  mul_nonneg (add_nonneg (rpt_nonneg i x) (rpt_nonneg j x)) (Tseg_nonneg fst hdl hle h2 (enorm2_nonneg _))

lemma remTerm_le_B {i j : Fin k} {dl dh : ℝ} (fst : Bool) (hdl : 0 < dl)
    (x : Fin (mDim k) → ℝ) :
    remTerm k lo hi i j dl dh fst x ≤ Bfun dl dh fst (rpt k lo hi i x + rpt k lo hi j x) := by
  unfold remTerm Bfun
  have hχ : 0 ≤ rpt k lo hi i x + rpt k lo hi j x := add_nonneg (rpt_nonneg i x) (rpt_nonneg j x)
  rw [← mul_Tseg fst hχ]
  refine mul_le_mul_of_nonneg_left (Tseg_mono fst hdl ?_) hχ
  exact (enorm2_sub_le _ _).trans_eq (add_comm _ _)

lemma Bfun_nonneg {dl dh : ℝ} (fst : Bool) (hdl : 0 < dl) (hle : dl ≤ dh) (h2 : dl < 2) {χ : ℝ}
    (hχ : 0 ≤ χ) : 0 ≤ Bfun dl dh fst χ := by
  unfold Bfun
  have := lamT_nonneg dh fst
  have := muT_nonneg fst hle h2
  have : 0 ≤ min (χ ^ 2 / dl) (π * χ) := le_min (by positivity) (mul_nonneg Real.pi_pos.le hχ)
  positivity

lemma Bfun_mono {dl dh : ℝ} (fst : Bool) (hdl : 0 < dl) (hle : dl ≤ dh) (h2 : dl < 2) {χ χ' : ℝ}
    (hχ : 0 ≤ χ) (hχχ : χ ≤ χ') : Bfun dl dh fst χ ≤ Bfun dl dh fst χ' := by
  unfold Bfun
  have h1 := lamT_nonneg dh fst
  have h2' := muT_nonneg fst hle h2
  have hsq : χ ^ 2 ≤ χ' ^ 2 := pow_le_pow_left₀ hχ hχχ 2
  have : min (χ ^ 2 / dl) (π * χ) ≤ min (χ' ^ 2 / dl) (π * χ') :=
    min_le_min (div_le_div_of_nonneg_right hsq hdl.le) (mul_le_mul_of_nonneg_left hχχ Real.pi_pos.le)
  nlinarith [mul_le_mul_of_nonneg_left hsq h1, mul_le_mul_of_nonneg_left hχχ h2']

/-- the bounds for one pair -/
lemma pair_bounds (h : ∀ d, lo d < hi d) {i j : Fin k} (hij : i ≠ j) {dl dh : ℝ} (fst : Bool)
    (hdl : 0 < dl) (hle : dl ≤ dh) (h2 : dl < 2) :
    let m2 := fun j => m2pt (halfSides k lo hi j)
    let m4 := fun j => m4pt (halfSides k lo hi j)
    let E1 := √(m2 i) + √(m2 j)
    let E2 := m2 i + m2 j + 2 * √(m2 i) * √(m2 j)
    let E4 := 8 * (m4 i + m4 j)
    (∀ x ∈ rbox lo hi, remTerm k lo hi i j dl dh fst x ≤ Bfun dl dh fst (hdiag k lo hi i + hdiag k lo hi j)) ∧
    ∫ x, remTerm k lo hi i j dl dh fst x ∂unifBox lo hi ≤
      lamT dh fst * E2 + muT dl dh fst * E1 + min (E2 / dl) (π * E1) ∧
    ∫ x, remTerm k lo hi i j dl dh fst x ^ 2 ∂unifBox lo hi ≤
      3 * lamT dh fst ^ 2 * E4 + 3 * muT dl dh fst ^ 2 * E2 + 3 * min (E4 / dl ^ 2) (π ^ 2 * E2) := by
  intro m2 m4 E1 E2 E4
  have hP := unifBox_isProb h
  obtain ⟨hE1, hE2, hE4⟩ := chi_moments h hij
  set χ : (Fin (mDim k) → ℝ) → ℝ := fun x => rpt k lo hi i x + rpt k lo hi j x with hχdef
  have hχ0 : ∀ x, 0 ≤ χ x := fun x => add_nonneg (rpt_nonneg i x) (rpt_nonneg j x)
  have hχb : ∀ x ∈ rbox lo hi, χ x ≤ hdiag k lo hi i + hdiag k lo hi j :=
    fun x hx => add_le_add (rpt_le hx i) (rpt_le hx j)
  have hχc : Continuous χ := (continuous_rpt i).add (continuous_rpt j)
  set D := hdiag k lo hi i + hdiag k lo hi j
  have hD : 0 ≤ D := add_nonneg (hdiag_nonneg i) (hdiag_nonneg j)
  have iχn : ∀ n : ℕ, Integrable (fun x => χ x ^ n) (unifBox lo hi) := fun n =>
    int_of_bdd h (hχc.pow n).measurable.aestronglyMeasurable (D ^ n) fun x hx => by
      rw [abs_pow, abs_of_nonneg (hχ0 x)]; exact pow_le_pow_left₀ (hχ0 x) (hχb x hx) n
  have iχ : Integrable χ (unifBox lo hi) := by simpa using iχn 1
  have hL0 := lamT_nonneg dh fst
  have hU0 := muT_nonneg fst hle h2
  set L := lamT dh fst
  set U := muT dl dh fst
  have hcont := continuous_remTerm (lo := lo) (hi := hi) i j dl dh fst
  have hmin_c : Continuous fun x => min (χ x ^ 2 / dl) (π * χ x) :=
    ((hχc.pow 2).div_const dl).min (continuous_const.mul hχc)
  have iMin : Integrable (fun x => min (χ x ^ 2 / dl) (π * χ x)) (unifBox lo hi) :=
    int_of_bdd h hmin_c.measurable.aestronglyMeasurable (π * D) fun x hx => by
      rw [abs_of_nonneg (le_min (by have := hχ0 x; positivity) (mul_nonneg Real.pi_pos.le (hχ0 x)))]
      exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_left (hχb x hx) Real.pi_pos.le)
  have iMin2 : Integrable (fun x => min (χ x ^ 2 / dl) (π * χ x) ^ 2) (unifBox lo hi) :=
    int_of_bdd h (hmin_c.pow 2).measurable.aestronglyMeasurable ((π * D) ^ 2) fun x hx => by
      have h0 : 0 ≤ min (χ x ^ 2 / dl) (π * χ x) :=
        le_min (by have := hχ0 x; positivity) (mul_nonneg Real.pi_pos.le (hχ0 x))
      rw [abs_pow, abs_of_nonneg h0]
      exact pow_le_pow_left₀ h0 ((min_le_right _ _).trans
        (mul_le_mul_of_nonneg_left (hχb x hx) Real.pi_pos.le)) 2
  have iT : Integrable (remTerm k lo hi i j dl dh fst) (unifBox lo hi) :=
    int_of_bdd h hcont.measurable.aestronglyMeasurable (Bfun dl dh fst D) fun x hx => by
      rw [abs_of_nonneg (remTerm_nonneg fst hdl hle h2 x)]
      exact (remTerm_le_B (lo := lo) (hi := hi) (i := i) (j := j) (dh := dh) fst hdl x).trans (Bfun_mono fst hdl hle h2 (hχ0 x) (hχb x hx))
  have iT2 : Integrable (fun x => remTerm k lo hi i j dl dh fst x ^ 2) (unifBox lo hi) :=
    int_of_bdd h (hcont.pow 2).measurable.aestronglyMeasurable (Bfun dl dh fst D ^ 2) fun x hx => by
      rw [abs_pow, abs_of_nonneg (remTerm_nonneg fst hdl hle h2 x)]
      exact pow_le_pow_left₀ (remTerm_nonneg fst hdl hle h2 x)
        ((remTerm_le_B (lo := lo) (hi := hi) (i := i) (j := j) (dh := dh) fst hdl x).trans (Bfun_mono fst hdl hle h2 (hχ0 x) (hχb x hx))) 2
  -- `E min(χ²/d, πχ) ≤ min(Eχ²/d, πEχ)`
  have hEmin : ∫ x, min (χ x ^ 2 / dl) (π * χ x) ∂unifBox lo hi ≤ min (E2 / dl) (π * E1) := by
    refine le_min ?_ ?_
    · calc ∫ x, min (χ x ^ 2 / dl) (π * χ x) ∂unifBox lo hi ≤ ∫ x, χ x ^ 2 / dl ∂unifBox lo hi :=
            integral_mono iMin ((iχn 2).div_const dl) fun x => min_le_left _ _
        _ = (∫ x, χ x ^ 2 ∂unifBox lo hi) / dl := integral_div _ _
        _ ≤ E2 / dl := div_le_div_of_nonneg_right hE2 hdl.le
    · calc ∫ x, min (χ x ^ 2 / dl) (π * χ x) ∂unifBox lo hi ≤ ∫ x, π * χ x ∂unifBox lo hi :=
            integral_mono iMin (iχ.const_mul π) fun x => min_le_right _ _
        _ = π * ∫ x, χ x ∂unifBox lo hi := integral_const_mul _ _
        _ ≤ π * E1 := mul_le_mul_of_nonneg_left hE1 Real.pi_pos.le
  -- `E min(χ²/d, πχ)² ≤ min(Eχ⁴/d², π²Eχ²)`
  have hEmin2 : ∫ x, min (χ x ^ 2 / dl) (π * χ x) ^ 2 ∂unifBox lo hi ≤ min (E4 / dl ^ 2) (π ^ 2 * E2) := by
    have h0 : ∀ x, 0 ≤ min (χ x ^ 2 / dl) (π * χ x) := fun x =>
      le_min (by have := hχ0 x; positivity) (mul_nonneg Real.pi_pos.le (hχ0 x))
    refine le_min ?_ ?_
    · calc ∫ x, min (χ x ^ 2 / dl) (π * χ x) ^ 2 ∂unifBox lo hi ≤ ∫ x, χ x ^ 4 / dl ^ 2 ∂unifBox lo hi := by
            refine integral_mono iMin2 ((iχn 4).div_const _) fun x => ?_
            have := pow_le_pow_left₀ (h0 x) (min_le_left (χ x ^ 2 / dl) (π * χ x)) 2
            calc min (χ x ^ 2 / dl) (π * χ x) ^ 2 ≤ (χ x ^ 2 / dl) ^ 2 := this
              _ = χ x ^ 4 / dl ^ 2 := by ring
        _ = (∫ x, χ x ^ 4 ∂unifBox lo hi) / dl ^ 2 := integral_div _ _
        _ ≤ E4 / dl ^ 2 := div_le_div_of_nonneg_right hE4 (by positivity)
    · calc ∫ x, min (χ x ^ 2 / dl) (π * χ x) ^ 2 ∂unifBox lo hi ≤ ∫ x, π ^ 2 * χ x ^ 2 ∂unifBox lo hi := by
            refine integral_mono iMin2 ((iχn 2).const_mul _) fun x => ?_
            have := pow_le_pow_left₀ (h0 x) (min_le_right (χ x ^ 2 / dl) (π * χ x)) 2
            calc min (χ x ^ 2 / dl) (π * χ x) ^ 2 ≤ (π * χ x) ^ 2 := this
              _ = π ^ 2 * χ x ^ 2 := by ring
        _ = π ^ 2 * ∫ x, χ x ^ 2 ∂unifBox lo hi := integral_const_mul _ _
        _ ≤ π ^ 2 * E2 := mul_le_mul_of_nonneg_left hE2 (by positivity)
  refine ⟨fun x hx => (remTerm_le_B (lo := lo) (hi := hi) (i := i) (j := j) (dh := dh) fst hdl x).trans (Bfun_mono fst hdl hle h2 (hχ0 x) (hχb x hx)),
    ?_, ?_⟩
  · -- first moment
    have iB : Integrable (fun x => L * χ x ^ 2 + U * χ x + min (χ x ^ 2 / dl) (π * χ x)) (unifBox lo hi) :=
      (((iχn 2).const_mul L).add (iχ.const_mul U)).add iMin
    calc ∫ x, remTerm k lo hi i j dl dh fst x ∂unifBox lo hi
        ≤ ∫ x, (L * χ x ^ 2 + U * χ x + min (χ x ^ 2 / dl) (π * χ x)) ∂unifBox lo hi :=
          integral_mono iT iB fun x => remTerm_le_B (lo := lo) (hi := hi) (i := i) (j := j) (dh := dh) fst hdl x
      _ = L * ∫ x, χ x ^ 2 ∂unifBox lo hi + U * ∫ x, χ x ∂unifBox lo hi +
            ∫ x, min (χ x ^ 2 / dl) (π * χ x) ∂unifBox lo hi := by
          have i1 : Integrable (fun x => L * χ x ^ 2 + U * χ x) (unifBox lo hi) :=
            ((iχn 2).const_mul L).add (iχ.const_mul U)
          rw [integral_add i1 iMin, integral_add ((iχn 2).const_mul L) (iχ.const_mul U),
            integral_const_mul, integral_const_mul]
      _ ≤ L * E2 + U * E1 + min (E2 / dl) (π * E1) := by
          have := mul_le_mul_of_nonneg_left hE2 hL0
          have := mul_le_mul_of_nonneg_left hE1 hU0
          linarith
  · -- second moment
    have hpt : ∀ x, remTerm k lo hi i j dl dh fst x ^ 2 ≤
        3 * L ^ 2 * χ x ^ 4 + 3 * U ^ 2 * χ x ^ 2 + 3 * min (χ x ^ 2 / dl) (π * χ x) ^ 2 := by
      intro x
      have hB := remTerm_le_B (lo := lo) (hi := hi) (i := i) (j := j) (dh := dh) fst hdl x
      have h0 := remTerm_nonneg (lo := lo) (hi := hi) (i := i) (j := j) fst hdl hle h2 x
      have hsq := pow_le_pow_left₀ h0 hB 2
      refine hsq.trans ?_
      unfold Bfun
      set a := L * χ x ^ 2; set b := U * χ x; set c := min (χ x ^ 2 / dl) (π * χ x)
      have : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
      calc (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := this
        _ = 3 * L ^ 2 * χ x ^ 4 + 3 * U ^ 2 * χ x ^ 2 + 3 * c ^ 2 := by
          simp only [a, b]; ring
    have iR : Integrable (fun x => 3 * L ^ 2 * χ x ^ 4 + 3 * U ^ 2 * χ x ^ 2 +
        3 * min (χ x ^ 2 / dl) (π * χ x) ^ 2) (unifBox lo hi) :=
      (((iχn 4).const_mul _).add ((iχn 2).const_mul _)).add (iMin2.const_mul 3)
    calc ∫ x, remTerm k lo hi i j dl dh fst x ^ 2 ∂unifBox lo hi
        ≤ ∫ x, (3 * L ^ 2 * χ x ^ 4 + 3 * U ^ 2 * χ x ^ 2 + 3 * min (χ x ^ 2 / dl) (π * χ x) ^ 2)
            ∂unifBox lo hi := integral_mono iT2 iR hpt
      _ = 3 * L ^ 2 * ∫ x, χ x ^ 4 ∂unifBox lo hi + 3 * U ^ 2 * ∫ x, χ x ^ 2 ∂unifBox lo hi +
            3 * ∫ x, min (χ x ^ 2 / dl) (π * χ x) ^ 2 ∂unifBox lo hi := by
          have i1 : Integrable (fun x => 3 * L ^ 2 * χ x ^ 4 + 3 * U ^ 2 * χ x ^ 2) (unifBox lo hi) :=
            ((iχn 4).const_mul _).add ((iχn 2).const_mul _)
          rw [integral_add i1 (iMin2.const_mul 3), integral_add ((iχn 4).const_mul _) ((iχn 2).const_mul _),
            integral_const_mul, integral_const_mul, integral_const_mul]
      _ ≤ 3 * L ^ 2 * E4 + 3 * U ^ 2 * E2 + 3 * min (E4 / dl ^ 2) (π ^ 2 * E2) := by
          have := mul_le_mul_of_nonneg_left hE4 (by positivity : (0:ℝ) ≤ 3 * L ^ 2)
          have := mul_le_mul_of_nonneg_left hE2 (by positivity : (0:ℝ) ≤ 3 * U ^ 2)
          linarith

lemma abs_remTerm_le {i j : Fin k} {dl dh : ℝ} (fst : Bool) (hdl : 0 < dl) (hle : dl ≤ dh) (h2 : dl < 2)
    {x : Fin (mDim k) → ℝ} (hx : x ∈ rbox lo hi) :
    |remTerm k lo hi i j dl dh fst x| ≤ Bfun dl dh fst (hdiag k lo hi i + hdiag k lo hi j) := by
  rw [abs_of_nonneg (remTerm_nonneg fst hdl hle h2 x)]
  exact (remTerm_le_B (dh := dh) fst hdl x).trans (Bfun_mono fst hdl hle h2
    (add_nonneg (rpt_nonneg i x) (rpt_nonneg j x)) (add_le_add (rpt_le hx i) (rpt_le hx j)))

end Pair

/-! ## `RemMomentsProp` -/

theorem remMomentsProp : RemMomentsProp := by
  intro k lo hi eps dlo dhi first h hd c ρ m2 m4 E1 E2 E4 ν L U
  have hP := unifBox_isProb h
  -- the summands
  set F : Fin k × Fin k → (Fin (mDim k) → ℝ) → ℝ := fun p x =>
    if p.1 < p.2 ∧ dlo p.1 p.2 < 2 then
      ν p.1 p.2 * remTerm k lo hi p.1 p.2 (dlo p.1 p.2) (dhi p.1 p.2) (first p.1 p.2) x
    else 0 with hFdef
  have hρ : ∀ x, ρ x = ∑ p : Fin k × Fin k, F p x := by
    intro x
    rw [Fintype.sum_prod_type]
    simp only [ρ, vertexRemSeg, hFdef]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · simp only [remTerm, rpt, cfgC, ν, c]; ring
    · rfl
  have hν : ∀ i j, 0 ≤ ν i j := fun i j => Nat.cast_nonneg _
  -- bounds on the box, continuity, integrability
  set Cb : Fin k × Fin k → ℝ := fun p =>
    if p.1 < p.2 ∧ dlo p.1 p.2 < 2 then
      ν p.1 p.2 * Bfun (dlo p.1 p.2) (dhi p.1 p.2) (first p.1 p.2) (hdiag k lo hi p.1 + hdiag k lo hi p.2)
    else 0 with hCbdef
  have hFb : ∀ p, ∀ x ∈ rbox lo hi, |F p x| ≤ Cb p := by
    intro p x hx
    simp only [hFdef, hCbdef]
    split_ifs with hc
    · obtain ⟨hdl, hle⟩ := hd p.1 p.2 hc.1 hc.2
      rw [abs_mul, abs_of_nonneg (hν _ _)]
      exact mul_le_mul_of_nonneg_left (abs_remTerm_le _ hdl hle hc.2 hx) (hν _ _)
    · simp
  have hFc : ∀ p, Continuous (F p) := by
    intro p
    simp only [hFdef]
    split_ifs
    · exact continuous_const.mul (continuous_remTerm _ _ _ _ _)
    · exact continuous_const
  have hF0 : ∀ p x, 0 ≤ F p x := by
    intro p x
    simp only [hFdef]
    split_ifs with hc
    · obtain ⟨hdl, hle⟩ := hd p.1 p.2 hc.1 hc.2
      exact mul_nonneg (hν _ _) (remTerm_nonneg _ hdl hle hc.2 x)
    · exact le_rfl
  have iF : ∀ p, Integrable (F p) (unifBox lo hi) := fun p =>
    int_of_bdd h (hFc p).measurable.aestronglyMeasurable (Cb p) (hFb p)
  have iFF : ∀ p q, Integrable (fun x => F p x * F q x) (unifBox lo hi) := fun p q =>
    int_of_bdd h ((hFc p).mul (hFc q)).measurable.aestronglyMeasurable (Cb p * Cb q) fun x hx => by
      rw [abs_mul]
      exact mul_le_mul (hFb p x hx) (hFb q x hx) (abs_nonneg _) ((abs_nonneg _).trans (hFb p x hx))
  have hρc : Continuous ρ := by
    have : ρ = fun x => ∑ p : Fin k × Fin k, F p x := funext hρ
    rw [this]; exact continuous_finsetSum _ fun p _ => hFc p
  -- the bound of each summand
  have hEF : ∀ p, ∫ x, F p x ∂unifBox lo hi ≤
      if p.1 < p.2 ∧ dlo p.1 p.2 < 2 then
        ν p.1 p.2 * (L p.1 p.2 * E2 p.1 p.2 + U p.1 p.2 * E1 p.1 p.2 +
          min (E2 p.1 p.2 / dlo p.1 p.2) (π * E1 p.1 p.2)) else 0 := by
    intro p
    simp only [hFdef]
    split_ifs with hc
    · obtain ⟨hdl, hle⟩ := hd p.1 p.2 hc.1 hc.2
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (pair_bounds h (ne_of_lt hc.1) _ hdl hle hc.2).2.1 (hν _ _)
    · simp
  have hEF2 : ∀ p, √(∫ x, F p x ^ 2 ∂unifBox lo hi) ≤
      if p.1 < p.2 ∧ dlo p.1 p.2 < 2 then
        ν p.1 p.2 * √(3 * L p.1 p.2 ^ 2 * E4 p.1 p.2 + 3 * U p.1 p.2 ^ 2 * E2 p.1 p.2 +
          3 * min (E4 p.1 p.2 / dlo p.1 p.2 ^ 2) (π ^ 2 * E2 p.1 p.2)) else 0 := by
    intro p
    simp only [hFdef]
    split_ifs with hc
    · obtain ⟨hdl, hle⟩ := hd p.1 p.2 hc.1 hc.2
      have hb := (pair_bounds h (ne_of_lt hc.1) (first p.1 p.2) hdl hle hc.2).2.2
      simp_rw [mul_pow]
      rw [integral_const_mul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hν _ _)]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hb) (hν _ _)
    · simp
  have hvpos := volume_rbox_toReal_pos h
  refine ⟨hρc.measurable, fun x => by rw [hρ x]; exact Finset.sum_nonneg fun p _ => hF0 p x, ?_, ?_⟩
  · -- first moment
    rw [setIntegral_rbox h, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ hvpos.le
    simp_rw [hρ]
    rw [integral_finsetSum _ fun p _ => iF p, ← Fintype.sum_prod_type']
    exact Finset.sum_le_sum fun p _ => hEF p
  · -- second moment
    rw [setIntegral_rbox h, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ hvpos.le
    simp_rw [hρ]
    refine (integral_sum_sq_le Finset.univ F iFF).trans ?_
    rw [← Fintype.sum_prod_type']
    refine pow_le_pow_left₀ (Finset.sum_nonneg fun p _ => Real.sqrt_nonneg _)
      (Finset.sum_le_sum fun p _ => hEF2 p) 2

end BHH
