/-
Module B (union area), part 6: the loops of `pairArcs` and `arcsOf`.

`pairArcs_spec`: if `pairArcs` succeeds, all centres are distinct, every recorded triple `(i, j, ar)` has `i < j`, an
overlapping pair of disks and `certArc ... = some ar`, and every overlapping pair `i < j` is recorded.
`arcsOfS` is `arcsOf` with the covered set attached to each arc.
-/
import BHH.UnionSound.Circle

open BHH.Cert Real Set

namespace BHH

noncomputable section

namespace US

/-! ## the pair loop -/

/-- `x`-component of `c_j - c_i` (fixed point) -/
def wxOf (pts : List (ℤ × ℤ)) (i j : ℕ) : ℤ := (pts.getD j (0, 0)).1 - (pts.getD i (0, 0)).1
/-- `y`-component of `c_j - c_i` (fixed point) -/
def wyOf (pts : List (ℤ × ℤ)) (i j : ℕ) : ℤ := (pts.getD j (0, 0)).2 - (pts.getD i (0, 0)).2
/-- `|c_j - c_i|²` (fixed point, scale `2^-2PR`) -/
def d2Of (pts : List (ℤ × ℤ)) (i j : ℕ) : ℤ := wxOf pts i j * wxOf pts i j + wyOf pts i j * wyOf pts i j

/-- one step of the inner loop of `pairArcs` -/
def pstep (cs : ℤ → Iv × Iv) (pts : List (ℤ × ℤ)) (R : ℤ) (cand : CandFn) (i j : ℕ)
    (lst : List (ℕ × ℕ × Arc)) : Option (List (ℕ × ℕ × Arc)) :=
  if d2Of pts i j == 0 then none
  else if 4 * R * R ≤ d2Of pts i j then some lst
  else match certArc cs (wxOf pts i j) (wyOf pts i j) (d2Of pts i j) R cand with
    | none => none
    | some ar => some ((i, j, ar) :: lst)

/-- the inner loop of `pairArcs` -/
def innerFold (cs : ℤ → Iv × Iv) (pts : List (ℤ × ℤ)) (R : ℤ) (cand : CandFn) (i : ℕ) (js : List ℕ)
    (rest : List (ℕ × ℕ × Arc)) : Option (List (ℕ × ℕ × Arc)) :=
  js.foldr (fun j acc2 => match acc2 with
    | none => none
    | some lst => pstep cs pts R cand i j lst) (some rest)

/-- the outer loop of `pairArcs` -/
def outerFold (cs : ℤ → Iv × Iv) (pts : List (ℤ × ℤ)) (R : ℤ) (cand : CandFn) (is : List ℕ) :
    Option (List (ℕ × ℕ × Arc)) :=
  is.foldr (fun i acc => match acc with
    | none => none
    | some rest => innerFold cs pts R cand i ((List.range pts.length).filter (fun j => i < j)) rest) (some [])

lemma pairArcs_eq (cs : ℤ → Iv × Iv) (pts : List (ℤ × ℤ)) (R : ℤ) (cand : CandFn) :
    pairArcs cs pts R cand = outerFold cs pts R cand (List.range pts.length) := rfl

lemma innerFold_cons (cs : ℤ → Iv × Iv) (pts : List (ℤ × ℤ)) (R : ℤ) (cand : CandFn) (i j : ℕ) (js : List ℕ)
    (rest : List (ℕ × ℕ × Arc)) : innerFold cs pts R cand i (j :: js) rest =
      match innerFold cs pts R cand i js rest with
      | none => none
      | some lst => pstep cs pts R cand i j lst := rfl

lemma outerFold_cons (cs : ℤ → Iv × Iv) (pts : List (ℤ × ℤ)) (R : ℤ) (cand : CandFn) (i : ℕ) (is : List ℕ) :
    outerFold cs pts R cand (i :: is) =
      match outerFold cs pts R cand is with
      | none => none
      | some rest => innerFold cs pts R cand i ((List.range pts.length).filter (fun j => i < j)) rest := rfl

lemma inner_spec (cs : ℤ → Iv × Iv) (pts : List (ℤ × ℤ)) (R : ℤ) (cand : CandFn) (i : ℕ) :
    ∀ (js : List ℕ) (rest lst : List (ℕ × ℕ × Arc)), innerFold cs pts R cand i js rest = some lst →
    (∀ j ∈ js, d2Of pts i j ≠ 0) ∧
    (∀ x ∈ lst, x ∈ rest ∨ (x.1 = i ∧ x.2.1 ∈ js ∧ ¬(4 * R * R ≤ d2Of pts i x.2.1) ∧
        certArc cs (wxOf pts i x.2.1) (wyOf pts i x.2.1) (d2Of pts i x.2.1) R cand = some x.2.2)) ∧
    (∀ j ∈ js, ¬(4 * R * R ≤ d2Of pts i j) → ∃ ar, (i, j, ar) ∈ lst) ∧
    (∀ x ∈ rest, x ∈ lst)
  | [], rest, lst, h => by
    simp only [innerFold, List.foldr_nil, Option.some.injEq] at h
    subst h
    exact ⟨by simp, fun x hx => Or.inl hx, by simp, fun x hx => hx⟩
  | j :: js, rest, lst, h => by
    rw [innerFold_cons] at h
    rcases hrec : innerFold cs pts R cand i js rest with _ | lst'
    · rw [hrec] at h; exact absurd h (by simp)
    · rw [hrec] at h
      simp only at h
      obtain ⟨ih1, ih2, ih3, ih4⟩ := inner_spec cs pts R cand i js rest lst' hrec
      unfold pstep at h
      split_ifs at h with hd hR'
      · simp only [Option.some.injEq] at h
        subst h
        refine ⟨?_, ?_, ?_, ih4⟩
        · intro j' hj'
          rcases List.mem_cons.mp hj' with rfl | hj'
          · simpa using hd
          · exact ih1 j' hj'
        · intro x hx
          rcases ih2 x hx with h | ⟨h1, h2, h3, h4⟩
          · exact Or.inl h
          · exact Or.inr ⟨h1, List.mem_cons_of_mem _ h2, h3, h4⟩
        · intro j' hj' hR''
          rcases List.mem_cons.mp hj' with rfl | hj'
          · exact absurd hR' hR''
          · exact ih3 j' hj' hR''
      · rcases hc : certArc cs (wxOf pts i j) (wyOf pts i j) (d2Of pts i j) R cand with _ | ar
        · rw [hc] at h; exact absurd h (by simp)
        · rw [hc] at h
          simp only [Option.some.injEq] at h
          subst h
          refine ⟨?_, ?_, ?_, fun x hx => List.mem_cons_of_mem _ (ih4 x hx)⟩
          · intro j' hj'
            rcases List.mem_cons.mp hj' with rfl | hj'
            · simpa using hd
            · exact ih1 j' hj'
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact Or.inr ⟨rfl, List.mem_cons_self, hR', hc⟩
            · rcases ih2 x hx with h | ⟨h1, h2, h3, h4⟩
              · exact Or.inl h
              · exact Or.inr ⟨h1, List.mem_cons_of_mem _ h2, h3, h4⟩
          · intro j' hj' hR''
            rcases List.mem_cons.mp hj' with rfl | hj'
            · exact ⟨ar, List.mem_cons_self⟩
            · obtain ⟨ar', h'⟩ := ih3 j' hj' hR''
              exact ⟨ar', List.mem_cons_of_mem _ h'⟩

lemma mem_filter_lt {i j n : ℕ} : j ∈ (List.range n).filter (fun j => i < j) ↔ j < n ∧ i < j := by
  simp [List.mem_filter, List.mem_range]

lemma outer_spec (cs : ℤ → Iv × Iv) (pts : List (ℤ × ℤ)) (R : ℤ) (cand : CandFn) :
    ∀ (is : List ℕ) (pa : List (ℕ × ℕ × Arc)), outerFold cs pts R cand is = some pa →
    (∀ i ∈ is, ∀ j, i < j → j < pts.length → d2Of pts i j ≠ 0) ∧
    (∀ x ∈ pa, x.1 ∈ is ∧ x.1 < x.2.1 ∧ x.2.1 < pts.length ∧ ¬(4 * R * R ≤ d2Of pts x.1 x.2.1) ∧
        certArc cs (wxOf pts x.1 x.2.1) (wyOf pts x.1 x.2.1) (d2Of pts x.1 x.2.1) R cand = some x.2.2) ∧
    (∀ i ∈ is, ∀ j, i < j → j < pts.length → ¬(4 * R * R ≤ d2Of pts i j) → ∃ ar, (i, j, ar) ∈ pa)
  | [], pa, h => by
    simp only [outerFold, List.foldr_nil, Option.some.injEq] at h
    subst h
    exact ⟨by simp, by simp, by simp⟩
  | i :: is, pa, h => by
    rw [outerFold_cons] at h
    rcases hrec : outerFold cs pts R cand is with _ | rest
    · rw [hrec] at h; exact absurd h (by simp)
    · rw [hrec] at h
      simp only at h
      obtain ⟨ih1, ih2, ih3⟩ := outer_spec cs pts R cand is rest hrec
      obtain ⟨k1, k2, k3, k4⟩ := inner_spec cs pts R cand i _ rest pa h
      refine ⟨?_, ?_, ?_⟩
      · intro i' hi' j hij hj
        rcases List.mem_cons.mp hi' with rfl | hi'
        · exact k1 j (mem_filter_lt.mpr ⟨hj, hij⟩)
        · exact ih1 i' hi' j hij hj
      · intro x hx
        rcases k2 x hx with h | ⟨h1, h2, h3, h4⟩
        · obtain ⟨a1, a2, a3, a4, a5⟩ := ih2 x h
          exact ⟨List.mem_cons_of_mem _ a1, a2, a3, a4, a5⟩
        · obtain ⟨b1, b2⟩ := mem_filter_lt.mp h2
          subst h1
          exact ⟨List.mem_cons_self, b2, b1, h3, h4⟩
      · intro i' hi' j hij hj hR'
        rcases List.mem_cons.mp hi' with rfl | hi'
        · exact k3 j (mem_filter_lt.mpr ⟨hj, hij⟩) hR'
        · obtain ⟨ar, h'⟩ := ih3 i' hi' j hij hj hR'
          exact ⟨ar, k4 _ h'⟩

/-- what a successful `pairArcs` gives -/
theorem pairArcs_spec {cs : ℤ → Iv × Iv} {pts : List (ℤ × ℤ)} {R : ℤ} {cand : CandFn}
    {pa : List (ℕ × ℕ × Arc)} (h : pairArcs cs pts R cand = some pa) :
    (∀ i j, i < j → j < pts.length → d2Of pts i j ≠ 0) ∧
    (∀ x ∈ pa, x.1 < x.2.1 ∧ x.2.1 < pts.length ∧ ¬(4 * R * R ≤ d2Of pts x.1 x.2.1) ∧
        certArc cs (wxOf pts x.1 x.2.1) (wyOf pts x.1 x.2.1) (d2Of pts x.1 x.2.1) R cand = some x.2.2) ∧
    (∀ i j, i < j → j < pts.length → ¬(4 * R * R ≤ d2Of pts i j) → ∃ ar, (i, j, ar) ∈ pa) := by
  rw [pairArcs_eq] at h
  obtain ⟨h1, h2, h3⟩ := outer_spec cs pts R cand _ pa h
  refine ⟨fun i j hij hj => h1 i (List.mem_range.mpr (lt_trans hij hj)) j hij hj, ?_,
    fun i j hij hj => h3 i (List.mem_range.mpr (lt_trans hij hj)) j hij hj⟩
  intro x hx
  obtain ⟨-, a2, a3, a4, a5⟩ := h2 x hx
  exact ⟨a2, a3, a4, a5⟩

/-! ## the arcs of one circle, with their covered sets -/

/-- `arcsOf` with the covered set of each arc (`Cov k l`: the directions of circle `k` covered by disk `l`) -/
def arcsOfS (Cov : ℕ → ℕ → Set ℝ) (pa : List (ℕ × ℕ × Arc)) (i : ℕ) : List (Arc × Set ℝ) :=
  pa.foldr (fun x acc =>
    if x.1 == i then (x.2.2, Cov x.1 x.2.1) :: acc
    else if x.2.1 == i then (shiftArc x.2.2, Cov x.2.1 x.1) :: acc
    else acc) []

lemma arcsOfS_cons (Cov : ℕ → ℕ → Set ℝ) (a b : ℕ) (ar : Arc) (pa : List (ℕ × ℕ × Arc)) (i : ℕ) :
    arcsOfS Cov ((a, b, ar) :: pa) i =
      if a == i then (ar, Cov a b) :: arcsOfS Cov pa i
      else if b == i then (shiftArc ar, Cov b a) :: arcsOfS Cov pa i
      else arcsOfS Cov pa i := rfl

lemma arcsOf_cons (a b : ℕ) (ar : Arc) (pa : List (ℕ × ℕ × Arc)) (i : ℕ) :
    arcsOf ((a, b, ar) :: pa) i =
      if a == i then ar :: arcsOf pa i
      else if b == i then shiftArc ar :: arcsOf pa i
      else arcsOf pa i := rfl

lemma arcsOfS_map (Cov : ℕ → ℕ → Set ℝ) : ∀ (pa : List (ℕ × ℕ × Arc)) (i : ℕ),
    (arcsOfS Cov pa i).map Prod.fst = arcsOf pa i
  | [], _ => rfl
  | ⟨a, b, ar⟩ :: pa, i => by
    rw [arcsOfS_cons, arcsOf_cons]
    split_ifs <;> simp [arcsOfS_map Cov pa i]

lemma mem_arcsOfS {Cov : ℕ → ℕ → Set ℝ} {i : ℕ} {q : Arc × Set ℝ} : ∀ {pa : List (ℕ × ℕ × Arc)},
    q ∈ arcsOfS Cov pa i → ∃ x ∈ pa, (x.1 = i ∧ q = (x.2.2, Cov x.1 x.2.1)) ∨
      (x.1 ≠ i ∧ x.2.1 = i ∧ q = (shiftArc x.2.2, Cov x.2.1 x.1))
  | [], h => by simp [arcsOfS] at h
  | ⟨a, b, ar⟩ :: pa, h => by
    rw [arcsOfS_cons] at h
    have ih : q ∈ arcsOfS Cov pa i → ∃ x ∈ (a, b, ar) :: pa, (x.1 = i ∧ q = (x.2.2, Cov x.1 x.2.1)) ∨
        (x.1 ≠ i ∧ x.2.1 = i ∧ q = (shiftArc x.2.2, Cov x.2.1 x.1)) := fun h' => by
      obtain ⟨x, hx, hq⟩ := mem_arcsOfS h'
      exact ⟨x, List.mem_cons_of_mem _ hx, hq⟩
    split_ifs at h with h1 h2
    · rcases List.mem_cons.mp h with rfl | h
      · exact ⟨(a, b, ar), List.mem_cons_self, Or.inl ⟨by simpa using h1, rfl⟩⟩
      · exact ih h
    · rcases List.mem_cons.mp h with rfl | h
      · exact ⟨(a, b, ar), List.mem_cons_self, Or.inr ⟨by simpa using h1, by simpa using h2, rfl⟩⟩
      · exact ih h
    · exact ih h

lemma arcsOfS_mono {Cov : ℕ → ℕ → Set ℝ} {i : ℕ} {q : Arc × Set ℝ} {y : ℕ × ℕ × Arc}
    {pa : List (ℕ × ℕ × Arc)} (h : q ∈ arcsOfS Cov pa i) : q ∈ arcsOfS Cov (y :: pa) i := by
  obtain ⟨a, b, ar⟩ := y
  rw [arcsOfS_cons]
  split_ifs
  · exact List.mem_cons_of_mem _ h
  · exact List.mem_cons_of_mem _ h
  · exact h

lemma arcsOfS_mem_fst {Cov : ℕ → ℕ → Set ℝ} {i : ℕ} {x : ℕ × ℕ × Arc} : ∀ {pa : List (ℕ × ℕ × Arc)},
    x ∈ pa → x.1 = i → (x.2.2, Cov x.1 x.2.1) ∈ arcsOfS Cov pa i
  | [], h, _ => by simp at h
  | y :: pa, h, hi => by
    rcases List.mem_cons.mp h with rfl | h
    · obtain ⟨a, b, ar⟩ := x
      simp only at hi
      subst hi
      rw [arcsOfS_cons, if_pos (by simp)]
      exact List.mem_cons_self
    · exact arcsOfS_mono (arcsOfS_mem_fst h hi)

lemma arcsOfS_mem_snd {Cov : ℕ → ℕ → Set ℝ} {i : ℕ} {x : ℕ × ℕ × Arc} : ∀ {pa : List (ℕ × ℕ × Arc)},
    x ∈ pa → x.1 ≠ i → x.2.1 = i → (shiftArc x.2.2, Cov x.2.1 x.1) ∈ arcsOfS Cov pa i
  | [], h, _, _ => by simp at h
  | y :: pa, h, h1, h2 => by
    rcases List.mem_cons.mp h with rfl | h
    · obtain ⟨a, b, ar⟩ := x
      simp only at h1 h2
      subst h2
      rw [arcsOfS_cons, if_neg (by simpa using h1), if_pos (by simp)]
      exact List.mem_cons_self
    · exact arcsOfS_mono (arcsOfS_mem_snd h h1 h2)

end US

end

end BHH
