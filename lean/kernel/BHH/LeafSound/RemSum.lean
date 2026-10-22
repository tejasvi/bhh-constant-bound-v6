/-
Module D, part 7: the code's `remainder` (a fold over the pairs) bounds the three real sums over `i < j` with
`d⁻ < 2` (the right-hand sides of module C's `RemMaxProp` and `RemMomentsProp`).
-/
import BHH.LeafSound.RemPair

open BHH.Cert Real

noncomputable section

namespace BHH

lemma fx_add_nat_mul (u : ℤ) (n : ℕ) (v : ℤ) : fx (u + n * v) = fx u + n * fx v := by
  unfold fx; push_cast; ring

/-- the fold of `remainder` is absorbing at `none` -/
lemma rem_fold_none {α : Type*} (g : α → Option (ℕ × ℤ × ℤ × ℤ)) (l : List α) :
    l.foldl (fun acc x => match acc, g x with
      | some r, some (nv, a, b, c) => some (⟨r.Rmax + nv * a, r.Er + nv * b, r.sEr2 + nv * c⟩ : RemRes)
      | _, _ => none) none = none := by
  induction l with
  | nil => rfl
  | cons x l ih => simpa [List.foldl] using ih

/-- the fold of `remainder` sums the per-element contributions -/
lemma rem_fold_sum {α : Type*} (g : α → Option (ℕ × ℤ × ℤ × ℤ)) (X1 X2 X3 : α → ℝ) (l : List α)
    (hX : ∀ x ∈ l, ∀ nv a b c, g x = some (nv, a, b, c) →
      X1 x ≤ nv * fx a ∧ X2 x ≤ nv * fx b ∧ X3 x ≤ nv * fx c) :
    ∀ r0 rr, l.foldl (fun acc x => match acc, g x with
      | some r, some (nv, a, b, c) => some (⟨r.Rmax + nv * a, r.Er + nv * b, r.sEr2 + nv * c⟩ : RemRes)
      | _, _ => none) (some r0) = some rr →
      (l.map X1).sum ≤ fx rr.Rmax - fx r0.Rmax ∧ (l.map X2).sum ≤ fx rr.Er - fx r0.Er ∧
      (l.map X3).sum ≤ fx rr.sEr2 - fx r0.sEr2 := by
  induction l with
  | nil =>
    intro r0 rr h
    simp only [List.foldl, Option.some.injEq] at h
    subst h; simp
  | cons x l ih =>
    intro r0 rr h
    simp only [List.foldl] at h
    rcases hg : g x with _ | ⟨nv, a, b, c⟩
    · rw [hg] at h
      simp only at h
      rw [rem_fold_none] at h
      exact absurd h (by simp)
    · rw [hg] at h
      simp only at h
      obtain ⟨i1, i2, i3⟩ := ih (fun y hy => hX y (List.mem_cons_of_mem _ hy)) _ rr h
      obtain ⟨j1, j2, j3⟩ := hX x List.mem_cons_self nv a b c hg
      simp only [fx_add_nat_mul] at i1 i2 i3
      simp only [List.map_cons, List.sum_cons]
      exact ⟨by linarith, by linarith, by linarith⟩

/-- sums over `pairList` are sums over `i < j` -/
lemma sum_pairList (k : ℕ) (Y : ℕ × ℕ → ℝ) :
    ((pairList k).map Y).sum = ∑ i : Fin k, ∑ j : Fin k, if i < j then Y (i.val, j.val) else 0 := by
  have inner : ∀ i : ℕ, ((((List.range k).filter (fun j => i < j)).map (fun j => (i, j))).map Y).sum =
      ∑ j : Fin k, if i < j.val then Y (i, j.val) else 0 := by
    intro i
    rw [← Finset.sum_range (fun j => if i < j then Y (i, j) else 0), Finset.sum_eq_multiset_sum]
    simp only [Finset.range_val, Multiset.range, Multiset.map_coe, Multiset.sum_coe, List.map_map]
    rw [List.sum_map_ite]
    simp [Function.comp_def]
  have outer : ∀ l : List ℕ, ((l.foldr (fun i acc =>
      ((List.range k).filter (fun j => i < j)).map (fun j => (i, j)) ++ acc) []).map Y).sum =
      (l.map fun i => ∑ j : Fin k, if i < j.val then Y (i, j.val) else 0).sum := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih => simp only [List.foldr, List.map_append, List.sum_append, ih, inner, List.map_cons, List.sum_cons]
  unfold pairList
  rw [outer]
  simp only [Fin.lt_iff_val_lt_val]
  rw [← Finset.sum_range (fun i => ∑ j : Fin k, if i < j.val then Y (i, j.val) else 0), Finset.sum_eq_multiset_sum]
  simp only [Finset.range_val, Multiset.range, Multiset.map_coe, Multiset.sum_coe]

lemma mem_zip_map_self {α β : Type*} {l : List α} {f : α → β} {pd : α × β} (h : pd ∈ l.zip (l.map f)) :
    pd.1 ∈ l ∧ pd.2 = f pd.1 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
    rcases h with h | h
    · subst h; simp
    · obtain ⟨h1, h2⟩ := ih h; exact ⟨List.mem_cons_of_mem _ h1, h2⟩

lemma map_zip_map_self {α β γ : Type*} (l : List α) (f : α → β) (Y : α → γ) :
    (l.zip (l.map f)).map (fun pd => Y pd.1) = l.map Y := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- the code's choice of `(λ, μ)` for the pair `(i, j)`: the first when `(d⁺)² < 1.98²` -/
def codeFirst (k : ℕ) (lo hi : List ℤ) (i j : Fin k) : Bool :=
  decide ((d2minmax ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default)).2 < thr198)

/-- pairs with `d⁻ ≥ 2` contribute nothing -/
lemma remPair_skip {k : ℕ} {lo hi : List ℤ} {cs : ℤ → Iv × Iv} {asinC : AsinFn} (i j : Fin k)
    (hd : 2 ≤ √(dminSq (boxRects k lo hi i) (boxRects k lo hi j))) {nv : ℕ} {a b c : ℤ}
    (h : remPair cs asinC (ptBoxes k lo hi) ((ptBoxes k lo hi).map moments) i.val j.val
      (d2minmax ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default)).1
      (d2minmax ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default)).2 =
        some (nv, a, b, c)) : nv = 0 ∧ a = 0 ∧ b = 0 ∧ c = 0 := by
  have hmin := dminSq_rectOf ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default)
  have h4 : (4 : ℝ) ≤ dminSq (boxRects k lo hi i) (boxRects k lo hi j) := by
    have := Real.sq_sqrt (VertexRect.dminSq_nonneg (boxRects k lo hi i) (boxRects k lo hi j))
    nlinarith
  have hs : 4 * ONE * ONE ≤
      (d2minmax ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default)).1 := by
    have e := ONE_sq4_cast
    have h4' : ((4 * ONE * ONE : ℤ) : ℝ) / (2 : ℝ) ^ (2 * PR) ≤
        ((d2minmax ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default)).1 : ℝ) /
          (2 : ℝ) ^ (2 * PR) := by
      rw [e]; unfold boxRects at h4; rw [← hmin]; exact h4
    rw [div_le_div_iff_of_pos_right (by positivity)] at h4'
    exact_mod_cast h4'
  unfold remPair at h
  rw [if_pos hs] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  omega

/-- The code's remainder bounds the three real sums of modules C (`RemMaxProp`, `RemMomentsProp`). -/
theorem remainder_sound {k : ℕ} (hk : 3 ≤ k) {lo hi : List ℤ} (hv : ValidBox k lo hi)
    {cs : ℤ → Iv × Iv} (hcs : CosSinSound cs) (asinC : AsinFn) {rr : RemRes}
    (h : remainder cs asinC (ptBoxes k lo hi) (pairList k)
      ((pairList k).map fun (i, j) => d2minmax ((ptBoxes k lo hi).getD i default) ((ptBoxes k lo hi).getD j default))
      = some rr) :
    let R := boxRects k lo hi
    let first := codeFirst k lo hi
    let c : Fin k → Pt := fun i => (R i).centre
    let eps : Fin k → ℝ := fun i => (R i).eps
    let dlo : Fin k → Fin k → ℝ := fun i j => √(dminSq (R i) (R j))
    let dhi : Fin k → Fin k → ℝ := fun i j => √(dmaxSq (R i) (R j))
    let m2 := fun j => m2pt (halfSides k (realLo k lo) (realLo k hi) j)
    let m4 := fun j => m4pt (halfSides k (realLo k lo) (realLo k hi) j)
    let E1 := fun i j => √(m2 i) + √(m2 j)
    let E2 := fun i j => m2 i + m2 j + 2 * √(m2 i) * √(m2 j)
    let E4 := fun i j => 8 * (m4 i + m4 j)
    let ν := fun i j => (nuCountSeg c eps dlo dhi first i j : ℝ)
    let L := fun i j => lamT (dhi i j) (first i j)
    let U := fun i j => muT (dlo i j) (dhi i j) (first i j)
    (∑ i, ∑ j, if i < j ∧ dlo i j < 2 then
        ν i j * (eps i + eps j) * Tseg (dlo i j) (dhi i j) (first i j) (eps i + eps j) else 0) ≤ fx rr.Rmax ∧
    (∑ i, ∑ j, if i < j ∧ dlo i j < 2 then
        ν i j * (L i j * E2 i j + U i j * E1 i j + min (E2 i j / dlo i j) (π * E1 i j)) else 0) ≤ fx rr.Er ∧
    (∑ i, ∑ j, if i < j ∧ dlo i j < 2 then
        ν i j * √(3 * L i j ^ 2 * E4 i j + 3 * U i j ^ 2 * E2 i j +
          3 * min (E4 i j / dlo i j ^ 2) (π ^ 2 * E2 i j)) else 0) ≤ fx rr.sEr2 := by
  intro R first c eps dlo dhi m2 m4 E1 E2 E4 ν L U
  -- the three summands as functions of `(i, j) : ℕ × ℕ`
  let Z1 : Fin k → Fin k → ℝ := fun i j =>
    ν i j * (eps i + eps j) * Tseg (dlo i j) (dhi i j) (first i j) (eps i + eps j)
  let Z2 : Fin k → Fin k → ℝ := fun i j =>
    ν i j * (L i j * E2 i j + U i j * E1 i j + min (E2 i j / dlo i j) (π * E1 i j))
  let Z3 : Fin k → Fin k → ℝ := fun i j =>
    ν i j * √(3 * L i j ^ 2 * E4 i j + 3 * U i j ^ 2 * E2 i j + 3 * min (E4 i j / dlo i j ^ 2) (π ^ 2 * E2 i j))
  let lift : (Fin k → Fin k → ℝ) → ℕ × ℕ → ℝ := fun Z p =>
    if hp : p.1 < k ∧ p.2 < k then (if dlo ⟨p.1, hp.1⟩ ⟨p.2, hp.2⟩ < 2 then Z ⟨p.1, hp.1⟩ ⟨p.2, hp.2⟩ else 0) else 0
  have hlift : ∀ Z : Fin k → Fin k → ℝ, ((pairList k).map (lift Z)).sum =
      ∑ i, ∑ j, if i < j ∧ dlo i j < 2 then Z i j else 0 := by
    intro Z
    rw [sum_pairList]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [ite_and]
    simp only [lift, dif_pos (And.intro i.isLt j.isLt), Fin.eta]
  set pairs := pairList k with hpairs
  set f : ℕ × ℕ → ℤ × ℤ := fun (i, j) =>
    d2minmax ((ptBoxes k lo hi).getD i default) ((ptBoxes k lo hi).getD j default) with hf
  unfold remainder at h
  dsimp only at h
  have key := rem_fold_sum (fun pd => remPair cs asinC (ptBoxes k lo hi) ((ptBoxes k lo hi).map moments)
      pd.1.1 pd.1.2 pd.2.1 pd.2.2) (fun pd => lift Z1 pd.1) (fun pd => lift Z2 pd.1) (fun pd => lift Z3 pd.1)
      (pairs.zip (pairs.map f)) ?_ ⟨0, 0, 0⟩ rr h
  · simp only [map_zip_map_self, hlift, fx_zero, sub_zero] at key
    exact key
  intro pd hpd nv a b c' hpr
  obtain ⟨hmem, hd2⟩ := mem_zip_map_self hpd
  obtain ⟨⟨i0, j0⟩, d2⟩ := pd
  simp only at hmem hd2 hpr
  obtain ⟨hij0, hj0⟩ := mem_pairList.mp hmem
  have hi0 : i0 < k := by omega
  subst hd2
  set i : Fin k := ⟨i0, hi0⟩
  set j : Fin k := ⟨j0, hj0⟩
  have hpr' : remPair cs asinC (ptBoxes k lo hi) ((ptBoxes k lo hi).map moments) i.val j.val
      (d2minmax ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default)).1
      (d2minmax ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default)).2 =
        some (nv, a, b, c') := hpr
  simp only [lift, dif_pos (And.intro hi0 hj0)]
  by_cases hd : dlo i j < 2
  · have hd' : ∀ p q, dlo ⟨i0, p⟩ ⟨j0, q⟩ < 2 := fun _ _ => hd
    simp only [hd', ite_true]
    have := remPair_sound hk hv hcs asinC i j (Fin.mk_lt_mk.mpr hij0) first rfl hpr' hd
    simp only [VertexRect.nuCount_eq] at this
    exact this
  · have hd' : ∀ p q, ¬ dlo ⟨i0, p⟩ ⟨j0, q⟩ < 2 := fun _ _ => hd
    simp only [hd', ite_false]
    obtain ⟨h0, ha, hb, hc⟩ := remPair_skip i j (not_lt.mp hd) hpr'
    subst h0 ha hb hc
    simp

end BHH
