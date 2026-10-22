/-
Module D, part 3: the code's centre list is the configuration of the rectangle centres (exact centres on a valid box),
so `UnionSoundProp` encloses the union area and the gradient at the centre configuration.
-/
import BHH.LeafSound.BoxState

open BHH.Cert

namespace BHH

/-- the code's centre list -/
def ctrList (k : ℕ) (lo hi : List ℤ) : List (ℤ × ℤ) := (ptBoxes k lo hi).map fun P => (P.xc, P.yc)

lemma ctrList_length (k : ℕ) (lo hi : List ℤ) : (ctrList k lo hi).length = k := by
  simp [ctrList, ptBoxes]

lemma validBox_even {k : ℕ} {lo hi : List ℤ} (h : ValidBox k lo hi) {d : ℕ} (hd : d < mDim k) :
    Even (lo.getD d 0 + hi.getD d 0) := (h.2.2.1 d hd).2

lemma ctrList_getD (k : ℕ) (lo hi : List ℤ) (i : ℕ) :
    (ctrList k lo hi).getD i (0, 0) =
      (((ptBoxes k lo hi).getD i default).xc, ((ptBoxes k lo hi).getD i default).yc) := by
  unfold ctrList
  have : ((0:ℤ), (0:ℤ)) = ((default : PtBox).xc, (default : PtBox).yc) := rfl
  rw [this, List.getD_map]

lemma centre_rectOf (P : PtBox) (hx : Even (P.xl + P.xh)) (hy : Even (P.yl + P.yh)) :
    (rectOf P).centre = (fx P.xc, fx P.yc) := by
  unfold rectOf Rect.centre PtBox.xc PtBox.yc; rw [fx_half hx, fx_half hy]

/-- on a valid box every code rectangle has exact centres -/
lemma ptBoxes_even {k : ℕ} (hk : 3 ≤ k) {lo hi : List ℤ} (h : ValidBox k lo hi) (i : Fin k) :
    Even (((ptBoxes k lo hi).getD i.val default).xl + ((ptBoxes k lo hi).getD i.val default).xh) ∧
    Even (((ptBoxes k lo hi).getD i.val default).yl + ((ptBoxes k lo hi).getD i.val default).yh) := by
  have hm : mDim k = 2 * k - 3 := rfl
  rw [ptBoxes_getD]
  by_cases h0 : i.val = 0
  · simp [h0]
  · by_cases h1 : i.val = 1
    · simp only [h0, h1, ite_false, ite_true, listGet]
      exact ⟨validBox_even h (show 0 < mDim k by rw [hm]; omega), by simp⟩
    · simp only [h0, h1, ite_false, listGet]
      have hi := i.isLt
      exact ⟨validBox_even h (show 2 * i.val - 3 < mDim k by rw [hm]; omega),
        validBox_even h (show 2 * i.val - 2 < mDim k by rw [hm]; omega)⟩

/-- the centre configuration of the code equals the configuration of the rectangle centres -/
lemma ptsCfg_ctrList {k : ℕ} (hk : 3 ≤ k) {lo hi : List ℤ} (h : ValidBox k lo hi) (i : Fin k) :
    ptsCfg k (ctrList k lo hi) i = (boxRects k lo hi i).centre := by
  unfold ptsCfg
  rw [ctrList_getD]
  unfold boxRects
  obtain ⟨hx, hy⟩ := ptBoxes_even hk h i
  rw [centre_rectOf _ hx hy]

end BHH
