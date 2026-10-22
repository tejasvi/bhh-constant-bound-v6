/-
Module D, part 2b: the edge state of a box (code: `st`, `idx3`) and the g bound `gmin ≤ 2 g(G_1(y))` on the box.
-/
import BHH.LeafSound.Digits

open BHH.Cert

namespace BHH

/-! ## the pair list -/

lemma mem_pairList {k a b : ℕ} : (a, b) ∈ pairList k ↔ a < b ∧ b < k := by
  unfold pairList
  have key : ∀ (l : List ℕ), (a, b) ∈ l.foldr (fun i acc =>
      ((List.range k).filter (fun j => i < j)).map (fun j => (i, j)) ++ acc) [] ↔
      a ∈ l ∧ a < b ∧ b < k := by
    intro l
    induction l with
    | nil => simp
    | cons i rest ih =>
      simp only [List.foldr_cons, List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
        decide_eq_true_eq, Prod.mk.injEq, List.mem_cons, ih]
      constructor
      · rintro (⟨j, ⟨hj, hij⟩, rfl, rfl⟩ | ⟨h1, h2, h3⟩)
        · exact ⟨Or.inl rfl, hij, hj⟩
        · exact ⟨Or.inr h1, h2, h3⟩
      · rintro ⟨h1 | h1, h2, h3⟩
        · subst h1; exact Or.inl ⟨b, ⟨h3, h2⟩, rfl, rfl⟩
        · exact Or.inr ⟨h1, h2, h3⟩
  rw [key]; simp only [List.mem_range]; constructor
  · rintro ⟨_, h2, h3⟩; exact ⟨h2, h3⟩
  · rintro ⟨h2, h3⟩; exact ⟨by omega, h2, h3⟩

lemma pairList_get_lt {k p : ℕ} (hp : p < (pairList k).length) :
    ((pairList k)[p]).1 < ((pairList k)[p]).2 ∧ ((pairList k)[p]).2 < k := by
  have h : (pairList k)[p] ∈ pairList k := List.getElem_mem hp
  have h2 : (((pairList k)[p]).1, ((pairList k)[p]).2) ∈ pairList k := by simpa using h
  exact mem_pairList.mp h2

/-! ## edge bitmasks -/

/-- the value of a bit list (bit `p` has weight `2^p`) -/
def val2 : List Bool → ℕ
  | [] => 0
  | b :: rest => (if b then 1 else 0) + 2 * val2 rest

lemma val2_testBit : ∀ (bs : List Bool) (p : ℕ), (val2 bs).testBit p = bs.getD p false
  | [], p => by simp [val2]
  | b :: rest, p => by
    cases p with
    | zero => cases b <;> simp [val2, Nat.testBit_zero] <;> omega
    | succ p =>
      simp only [val2, List.getD_cons_succ]
      rw [← val2_testBit rest p]
      rw [Nat.testBit_succ]
      congr 1
      cases b <;> simp <;> omega

lemma val2_lt : ∀ (bs : List Bool), val2 bs < 2 ^ bs.length
  | [] => by simp [val2]
  | b :: rest => by
    have := val2_lt rest
    simp only [val2, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

/-- the point `i` of a configuration, by a natural number index (0 outside) -/
def ptN {k : ℕ} (y : Fin k → Pt) (i : ℕ) : Pt := if h : i < k then y ⟨i, h⟩ else 0

/-- the edge bitmask of the unit-distance graph of `y` (bit `p` for the pair `(pairList k)[p]`) -/
noncomputable def edgeBits (k : ℕ) (y : Fin k → Pt) : ℕ := by
  classical exact val2 ((pairList k).map fun ij => decide (sqDist (ptN y ij.1) (ptN y ij.2) ≤ 1))

lemma edgeBits_testBit (k : ℕ) (y : Fin k → Pt) {p : ℕ} (hp : p < (pairList k).length) :
    (edgeBits k y).testBit p ↔ sqDist (ptN y ((pairList k)[p]).1) (ptN y ((pairList k)[p]).2) ≤ 1 := by
  classical
  unfold edgeBits
  rw [val2_testBit]
  rw [List.getD_eq_getElem _ _ (by simpa using hp)]
  simp

lemma sqDist_comm (a b : Pt) : sqDist a b = sqDist b a := by unfold sqDist; ring

lemma graphOf_edgeBits (k : ℕ) (y : Fin k → Pt) : graphOf k (edgeBits k y) = unitGraph y := by
  ext i j
  simp only [graphOf, unitGraph]
  constructor
  · rintro ⟨hij, p, hp, hpair, hbit⟩
    refine ⟨hij, ?_⟩
    rw [edgeBits_testBit k y hp] at hbit
    rcases hpair with h | h
    · rw [List.getD_eq_getElem _ _ hp] at h
      rw [h] at hbit; simpa [ptN, i.isLt, j.isLt] using hbit
    · rw [List.getD_eq_getElem _ _ hp] at h
      rw [h] at hbit; rw [sqDist_comm]; simpa [ptN, i.isLt, j.isLt] using hbit
  · rintro ⟨hij, hd⟩
    refine ⟨hij, ?_⟩
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · have hm : (i.val, j.val) ∈ pairList k := mem_pairList.mpr ⟨h, j.isLt⟩
      obtain ⟨p, hp, hpe⟩ := List.mem_iff_getElem.mp hm
      refine ⟨p, hp, Or.inl (by rw [List.getD_eq_getElem _ _ hp, hpe]), ?_⟩
      rw [edgeBits_testBit k y hp, hpe]; simpa [ptN, i.isLt, j.isLt] using hd
    · have hm : (j.val, i.val) ∈ pairList k := mem_pairList.mpr ⟨h, i.isLt⟩
      obtain ⟨p, hp, hpe⟩ := List.mem_iff_getElem.mp hm
      refine ⟨p, hp, Or.inr (by rw [List.getD_eq_getElem _ _ hp, hpe]), ?_⟩
      rw [edgeBits_testBit k y hp, hpe]; rw [sqDist_comm] at hd; simpa [ptN, i.isLt, j.isLt] using hd

end BHH
