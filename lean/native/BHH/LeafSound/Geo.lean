/-
Module D, part 1: the geometry of a box as seen by the leaf code (`ptBoxes`, `d2minmax`, centres, half-widths) and the
real configuration `xcfg k x` of a point `x` of the box.
-/
import BHH.Ivl.Asin
import BHH.VertexRect

open MeasureTheory Set Real BHH.Cert

noncomputable section

namespace BHH

/-- the real rectangle of a code rectangle -/
def rectOf (P : PtBox) : Rect := ⟨fx P.xl, fx P.xh, fx P.yl, fx P.yh⟩

/-- the rectangles of the points of a box -/
def boxRects (k : ℕ) (lo hi : List ℤ) : Fin k → Rect := fun i => rectOf ((ptBoxes k lo hi).getD i.val default)

lemma fx_zero : fx 0 = 0 := by simp [fx]

lemma ptBoxes_getD (k : ℕ) (lo hi : List ℤ) (i : Fin k) :
    (ptBoxes k lo hi).getD i.val default =
      (if i.val = 0 then ⟨0, 0, 0, 0⟩
       else if i.val = 1 then ⟨listGet lo 0, listGet hi 0, 0, 0⟩
       else ⟨listGet lo (2 * i.val - 3), listGet hi (2 * i.val - 3), listGet lo (2 * i.val - 2),
             listGet hi (2 * i.val - 2)⟩) := by
  unfold ptBoxes
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp only [List.getElem_map, List.getElem_range]
  by_cases h0 : i.val = 0
  · simp [h0]
  · by_cases h1 : i.val = 1
    · simp [h1]
    · simp [h0, h1, beq_iff_eq]

/-- points of `boxOf` lie between the corners, coordinatewise -/
lemma mem_boxOf_iff {m : ℕ} {lo hi : List ℤ} {x : Fin m → ℝ} :
    x ∈ (boxOf lo hi : Set (Fin m → ℝ)) ↔ ∀ d : Fin m, fx (lo.getD d.val 0) ≤ x d ∧ x d < fx (hi.getD d.val 0) := by
  unfold boxOf; simp [Set.mem_pi, Set.mem_Ico]

lemma xget_of_lt {m : ℕ} (x : Fin m → ℝ) {d : ℕ} (h : d < m) : xget x d = x ⟨d, h⟩ := by
  simp [xget, h]

/-- the configuration of a point of the box lies in the code's rectangles -/
lemma mem_boxRects {k : ℕ} {lo hi : List ℤ} {x : Fin (mDim k) → ℝ} (hx : x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)))
    (hk : 3 ≤ k) (i : Fin k) : (boxRects k lo hi i).Mem (xcfg k x i) := by
  rw [mem_boxOf_iff] at hx
  have hm : mDim k = 2 * k - 3 := rfl
  unfold boxRects rectOf Rect.Mem
  rw [ptBoxes_getD]
  unfold xcfg
  by_cases h0 : i.val = 0
  · simp [h0, fx_zero]
  · by_cases h1 : i.val = 1
    · have h0m : 0 < mDim k := by rw [hm]; omega
      have := hx ⟨0, h0m⟩
      simp only [h0, h1, ite_false, ite_true, listGet]
      rw [xget_of_lt x h0m]
      exact ⟨this.1, this.2.le, by simp [fx_zero], by simp [fx_zero]⟩
    · have hi := i.isLt
      have ha : 2 * i.val - 3 < mDim k := by rw [hm]; omega
      have hb : 2 * i.val - 2 < mDim k := by rw [hm]; omega
      have h3 := hx ⟨2 * i.val - 3, ha⟩
      have h4 := hx ⟨2 * i.val - 2, hb⟩
      simp only [h0, h1, ite_false, listGet]
      rw [xget_of_lt x ha, xget_of_lt x hb]
      exact ⟨h3.1, h3.2.le, h4.1, h4.2.le⟩

/-- `fx` of a half sum is the half sum of `fx` when the sum is even -/
lemma fx_half {a b : ℤ} (h : Even (a + b)) : fx ((a + b) / 2) = (fx a + fx b) / 2 := by
  obtain ⟨r, hr⟩ := h
  have : (a + b) / 2 = r := by omega
  rw [this]; unfold fx
  have : (a : ℝ) + b = 2 * r := by exact_mod_cast (by omega : a + b = 2 * r)
  field_simp; linarith

/-! ## distances between the code rectangles -/

lemma fx_sub (a b : ℤ) : fx (a - b) = fx a - fx b := by unfold fx; push_cast; ring

lemma fx_max (a b : ℤ) : fx (Max.max a b) = Max.max (fx a) (fx b) := by
  unfold fx; rw [Int.cast_max, max_div_div_right (by positivity)]

lemma fx_abs (a : ℤ) : fx |a| = |fx a| := by
  unfold fx; rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 ^ PR), Int.cast_abs]

lemma gap_fx (a b c d : ℤ) : gap (fx a) (fx b) (fx c) (fx d) = fx (gapI a b c d) := by
  unfold gap gapI
  rw [fx_max, fx_max, fx_sub, fx_sub, fx_zero]

lemma span_fx (a b c d : ℤ) : span (fx a) (fx b) (fx c) (fx d) = fx (spanI a b c d) := by
  unfold span spanI
  push_cast
  rw [fx_max, fx_abs, fx_abs, fx_sub, fx_sub]

/-- the exact squared distances of the code, scaled: `(d^∓)^2 = d2 / 2^(2 PR)` -/
lemma dminSq_rectOf (P Q : PtBox) : dminSq (rectOf P) (rectOf Q) = ((d2minmax P Q).1 : ℝ) / (2 : ℝ) ^ (2 * PR) := by
  unfold dminSq rectOf d2minmax; simp only
  rw [gap_fx, gap_fx]; unfold fx; push_cast; ring

lemma dmaxSq_rectOf (P Q : PtBox) : dmaxSq (rectOf P) (rectOf Q) = ((d2minmax P Q).2 : ℝ) / (2 : ℝ) ^ (2 * PR) := by
  unfold dmaxSq rectOf d2minmax; simp only
  rw [span_fx, span_fx]; unfold fx; push_cast; ring

/-- edge present on the whole box when `d2max ≤ ONE²` -/
lemma sqDist_le_one_of {R S : Rect} {p q : Pt} (hp : R.Mem p) (hq : S.Mem q) (h : dmaxSq R S ≤ 1) :
    sqDist p q ≤ 1 :=
  le_trans (VertexRect.dminSq_le_sqDist hp hq).2 h

/-- edge absent on the whole box when `ONE² < d2min` -/
lemma one_lt_sqDist_of {R S : Rect} {p q : Pt} (hp : R.Mem p) (hq : S.Mem q) (h : 1 < dminSq R S) :
    1 < sqDist p q :=
  lt_of_lt_of_le h (VertexRect.dminSq_le_sqDist hp hq).1

end BHH
