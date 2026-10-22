/-
Module C: split of `ProbStripsProp` into a measure-theoretic part (`StripRealProp`) and a code part
(`StripCodeProp`), joined by the real strip values `innerVal`, `outerVal` below; the assembly
`probStripsProp_of_strip` is proved here.
-/
import BHH.Box.Props

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH

open BHH.Cert

/-- the strip endpoints of `probStrips`: `zx0 + ⌊wz t / 8⌋` with `zx0 = P.xl - Q.xh`, `wz = (P.xh - Q.xl) - zx0` -/
def stripX (P Q : PtBox) (t : ℕ) : ℤ := (P.xl - Q.xh) + ((P.xh - Q.xl) - (P.xl - Q.xh)) * (t : ℤ) / 8

/-- `max(|x0|, |x1|)` as in `probStrips` -/
def stripAmax (x0 x1 : ℤ) : ℕ := Max.max x0.natAbs x1.natAbs

/-- the least `|z|` over the strip as in `probStrips` -/
def stripAmin (x0 x1 : ℤ) : ℕ := if x0 ≤ 0 ∧ 0 ≤ x1 then 0 else Min.min x0.natAbs x1.natAbs

/-- inner half-height of the strip (`√(1 - amax²)`, rounded down) -/
def stripYbIn (x0 x1 : ℤ) : ℤ := (Iv.sqrt (Iv.sub (Iv.int 1) (Iv.sqr (Iv.pt (stripAmax x0 x1))))).lo

/-- outer half-height of the strip (`√(1 - amin²)`, rounded up) -/
def stripYbOut (x0 x1 : ℤ) : ℤ := (Iv.sqrt (Iv.sub (Iv.int 1) (Iv.sqr (Iv.pt (stripAmin x0 x1))))).hi

/-- distribution function of `Zx = X_i - X_j` (x-ranges of the rectangles `P`, `Q`) -/
def cdfX (P Q : PtBox) (z : ℝ) : ℝ := cdfR (fx P.xl) (fx P.xh) (fx Q.xl) (fx Q.xh) z

/-- distribution function of `Zy = Y_i - Y_j` -/
def cdfY (P Q : PtBox) (z : ℝ) : ℝ := cdfR (fx P.yl) (fx P.yh) (fx Q.yl) (fx Q.yh) z

/-- the real value of the inner staircase term of the strip `(x0, x1]` -/
def innerVal (P Q : PtBox) (x0 x1 : ℤ) : ℝ :=
  if (stripAmax x0 x1 : ℤ) < ONE ∧ 0 < stripYbIn x0 x1 then
    (cdfY P Q (fx (stripYbIn x0 x1)) - cdfY P Q (fx (-stripYbIn x0 x1))) *
      (cdfX P Q (fx x1) - cdfX P Q (fx x0))
  else 0

/-- the real value of the outer staircase term of the strip `(x0, x1]` -/
def outerVal (P Q : PtBox) (x0 x1 : ℤ) : ℝ :=
  if (stripAmin x0 x1 : ℤ) < ONE then
    (if P.yh = P.yl ∧ Q.yh = Q.yl then
        (if (P.yl - Q.yl).natAbs ≤ (stripYbOut x0 x1).toNat then 1 else 0)
      else cdfY P Q (fx (stripYbOut x0 x1)) - cdfY P Q (fx (-stripYbOut x0 x1))) *
      (cdfX P Q (fx x1) - cdfX P Q (fx x0))
  else 0

/-- measure-theoretic part: the staircase bounds for the edge events on a box -/
def StripRealProp : Prop :=
  ∀ (k : ℕ) (lo hi : List ℤ), ValidBox k lo hi → ∀ i j : Fin k, i < j →
    0 < ((ptBoxes k lo hi).getD i.val default).xh - ((ptBoxes k lo hi).getD j.val default).xl -
      (((ptBoxes k lo hi).getD i.val default).xl - ((ptBoxes k lo hi).getD j.val default).xh) →
    ENNReal.ofReal (Max.max (∑ t ∈ Finset.range 8,
        innerVal ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default)
          (stripX ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default) t)
          (stripX ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default) (t + 1))) 0 *
        (volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal) ≤
      volume {x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)) | sqDist (xcfg k x i) (xcfg k x j) ≤ 1} ∧
    ENNReal.ofReal (Max.max (1 - ∑ t ∈ Finset.range 8,
        outerVal ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default)
          (stripX ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default) t)
          (stripX ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default) (t + 1))) 0 *
        (volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal) ≤
      volume {x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)) | 1 < sqDist (xcfg k x i) (xcfg k x j)}

/-- code part: `probStrips` returns lower bounds of the real staircase values -/
def StripCodeProp : Prop :=
  ∀ P Q : PtBox, P.xl ≤ P.xh → P.yl ≤ P.yh → Q.xl ≤ Q.xh → Q.yl ≤ Q.yh →
    ((P.xh - Q.xl) - (P.xl - Q.xh) ≤ 0 → probStrips P Q = (0, 0)) ∧
    (0 < (P.xh - Q.xl) - (P.xl - Q.xh) →
      fx (probStrips P Q).1 ≤
        Max.max (∑ t ∈ Finset.range 8, innerVal P Q (stripX P Q t) (stripX P Q (t + 1))) 0 ∧
      fx (probStrips P Q).2 ≤
        Max.max (1 - ∑ t ∈ Finset.range 8, outerVal P Q (stripX P Q t) (stripX P Q (t + 1))) 0)

/-- the rectangles of a valid box are ordered (`xl ≤ xh`, `yl ≤ yh`) -/
lemma ptBoxes_ordered {k : ℕ} {lo hi : List ℤ} (hv : ValidBox k lo hi) (j : Fin k) :
    ((ptBoxes k lo hi).getD j.val default).xl ≤ ((ptBoxes k lo hi).getD j.val default).xh ∧
    ((ptBoxes k lo hi).getD j.val default).yl ≤ ((ptBoxes k lo hi).getD j.val default).yh := by
  have hj : (ptBoxes k lo hi).getD j.val default =
      if j.val == 0 then ⟨0, 0, 0, 0⟩
      else if j.val == 1 then ⟨listGet lo 0, listGet hi 0, 0, 0⟩
      else ⟨listGet lo (2 * j.val - 3), listGet hi (2 * j.val - 3), listGet lo (2 * j.val - 2),
        listGet hi (2 * j.val - 2)⟩ := by
    simp [ptBoxes, List.getD_eq_getElem?_getD, j.isLt]
  have hlt : ∀ d < mDim k, lo.getD d 0 < hi.getD d 0 := fun d hd => (hv.2.2.1 d hd).1
  rw [hj]
  have hk := j.isLt
  split_ifs with h0 h1
  · exact ⟨le_rfl, le_rfl⟩
  · simp only [beq_iff_eq] at h1
    exact ⟨(hlt 0 (by unfold mDim; omega)).le, le_rfl⟩
  · simp only [beq_iff_eq] at h0 h1
    exact ⟨(hlt _ (by unfold mDim; omega)).le, (hlt _ (by unfold mDim; omega)).le⟩

/-- the assembly: `StripRealProp` and `StripCodeProp` give `ProbStripsProp` -/
theorem probStripsProp_of_strip (hR : StripRealProp) (hC : StripCodeProp) : ProbStripsProp := by
  intro k lo hi hv i j hij
  obtain ⟨hPx, hPy⟩ := ptBoxes_ordered hv i
  obtain ⟨hQx, hQy⟩ := ptBoxes_ordered hv j
  obtain ⟨hz, hpos⟩ := hC _ _ hPx hPy hQx hQy
  have hv0 : 0 ≤ (volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal := ENNReal.toReal_nonneg
  by_cases hw : ((ptBoxes k lo hi).getD i.val default).xh - ((ptBoxes k lo hi).getD j.val default).xl -
      (((ptBoxes k lo hi).getD i.val default).xl - ((ptBoxes k lo hi).getD j.val default).xh) ≤ 0
  · rw [hz hw]
    simp only [fx, Int.cast_zero, zero_div, zero_mul, ENNReal.ofReal_zero]
    exact ⟨zero_le, zero_le⟩
  · push Not at hw
    obtain ⟨h1, h2⟩ := hpos hw
    obtain ⟨r1, r2⟩ := hR k lo hi hv i j hij hw
    exact ⟨(ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h1 hv0)).trans r1,
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h2 hv0)).trans r2⟩

end BHH
