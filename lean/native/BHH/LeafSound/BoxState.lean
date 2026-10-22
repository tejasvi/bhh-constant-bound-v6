/-
Module D, part 2c: the code's edge state of a valid box is completed by the edge set of every configuration of the box,
so the g table bounds `2 g(G_1(y))` from below on the box (and on the events of one or two undetermined edges).
-/
import BHH.LeafSound.GraphState

open BHH.Cert

namespace BHH

/-- the code's edge states of a box (`st` of `leafLB`): 1 present, 0 absent, 2 undetermined -/
def stCode (k : ℕ) (lo hi : List ℤ) : List ℕ :=
  ((pairList k).map fun ij => d2minmax ((ptBoxes k lo hi).getD ij.1 default) ((ptBoxes k lo hi).getD ij.2 default)).map
    fun mm => if mm.2 ≤ ONE * ONE then 1 else if ONE * ONE < mm.1 then 0 else 2

lemma stCode_length (k : ℕ) (lo hi : List ℤ) : (stCode k lo hi).length = (pairList k).length := by
  simp [stCode]

lemma stCode_lt3 (k : ℕ) (lo hi : List ℤ) : ∀ s ∈ stCode k lo hi, s < 3 := by
  intro s hs
  simp only [stCode, List.mem_map] at hs
  obtain ⟨_, _, rfl⟩ := hs
  split_ifs <;> norm_num

lemma stCode_getD (k : ℕ) (lo hi : List ℤ) {p : ℕ} (hp : p < (pairList k).length) :
    (stCode k lo hi).getD p 0 =
      (let mm := d2minmax ((ptBoxes k lo hi).getD ((pairList k)[p]).1 default)
          ((ptBoxes k lo hi).getD ((pairList k)[p]).2 default)
       if mm.2 ≤ ONE * ONE then 1 else if ONE * ONE < mm.1 then 0 else 2) := by
  rw [List.getD_eq_getElem _ _ (by rw [stCode_length]; exact hp)]
  simp [stCode]

/-- the scale relation `ONE² ↔ 2^(2 PR)` -/
lemma ONE_sq_cast : ((ONE * ONE : ℤ) : ℝ) = (2 : ℝ) ^ (2 * PR) := by
  push_cast; rw [ONE_cast]; unfold SC; ring

/-- on a valid box, the configuration of every point realizes the code's present/absent edges -/
lemma completes_stCode {k : ℕ} (hk : 3 ≤ k) {lo hi : List ℤ} {x : Fin (mDim k) → ℝ}
    (hx : x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ))) :
    Completes k (val3 (stCode k lo hi)) (edgeBits k (xcfg k x)) := by
  classical
  refine ⟨?_, ?_⟩
  · have := val2_lt ((pairList k).map fun ij => decide (sqDist (ptN (xcfg k x) ij.1) (ptN (xcfg k x) ij.2) ≤ 1))
    simpa [edgeBits] using this
  · intro p hp
    have hd := val3_digit (stCode k lo hi) (stCode_lt3 k lo hi) p (by rw [stCode_length]; exact hp)
    rw [hd, stCode_getD k lo hi hp]
    obtain ⟨hij, hjk⟩ := pairList_get_lt hp
    set i := ((pairList k)[p]).1
    set j := ((pairList k)[p]).2
    have hik : i < k := lt_trans hij hjk
    have hRi := mem_boxRects hx hk ⟨i, hik⟩
    have hRj := mem_boxRects hx hk ⟨j, hjk⟩
    have hpi : ptN (xcfg k x) i = xcfg k x ⟨i, hik⟩ := by simp [ptN, hik]
    have hpj : ptN (xcfg k x) j = xcfg k x ⟨j, hjk⟩ := by simp [ptN, hjk]
    have hbi : boxRects k lo hi ⟨i, hik⟩ = rectOf ((ptBoxes k lo hi).getD i default) := rfl
    have hbj : boxRects k lo hi ⟨j, hjk⟩ = rectOf ((ptBoxes k lo hi).getD j default) := rfl
    rw [hbi] at hRi; rw [hbj] at hRj
    simp only
    constructor
    · intro h1
      split_ifs at h1 with hmx hmn
      · rw [edgeBits_testBit k _ hp, hpi, hpj]
        apply sqDist_le_one_of hRi hRj
        rw [dmaxSq_rectOf]
        rw [div_le_one (by positivity)]
        have : ((d2minmax ((ptBoxes k lo hi).getD i default) ((ptBoxes k lo hi).getD j default)).2 : ℝ)
            ≤ ((ONE * ONE : ℤ) : ℝ) := by exact_mod_cast hmx
        rwa [ONE_sq_cast] at this
      all_goals omega
    · intro h0
      split_ifs at h0 with hmx hmn
      rw [edgeBits_testBit k _ hp, hpi, hpj, not_le]
      apply one_lt_sqDist_of hRi hRj
      rw [dminSq_rectOf]
      rw [one_lt_div (by positivity)]
      have : ((ONE * ONE : ℤ) : ℝ) <
          ((d2minmax ((ptBoxes k lo hi).getD i default) ((ptBoxes k lo hi).getD j default)).1 : ℝ) := by
        exact_mod_cast hmn
      rwa [ONE_sq_cast] at this
      all_goals omega

/-- the g bound on a valid box -/
theorem gmin_le_two_g {k : ℕ} (hk : 3 ≤ k) {gt : GTab} (hgt : GTabSound k gt) {lo hi : List ℤ}
    {x : Fin (mDim k) → ℝ} (hx : x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ))) :
    (gt.gmin (val3 (stCode k lo hi)) : ℝ) ≤ 2 * dcG (unitGraph (xcfg k x)) := by
  have hc := completes_stCode hk hx
  have hidx : val3 (stCode k lo hi) < 3 ^ (pairList k).length := by
    have := val3_lt3 (stCode k lo hi) (stCode_lt3 k lo hi)
    rwa [stCode_length] at this
  have := hgt _ _ hidx hc
  rwa [graphOf_edgeBits] at this

end BHH
