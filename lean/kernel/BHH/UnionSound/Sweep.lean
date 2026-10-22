/-
Module B (union area), part 3: the sweep over the sorted endpoints.

`uSet PS L` is the union of the elementary intervals `[p, q)` of consecutive points of `L` that are not covered by a
piece of `PS` (the set the code integrates over).  `sumElems_spec`: `sumElems` encloses the integrals of the area
integrand, `cos` and `sin` over `uSet`.  `uSet_avoid_pieces`: `uSet` meets no open piece (when every piece endpoint
value occurs in `L`).  `uSet_cover`: a point between the first and the last point of `L` that is not in `uSet` lies
in a closed piece.
-/
import BHH.UnionSound.Pieces

open BHH.Cert Real Set MeasureTheory

namespace BHH

noncomputable section

namespace US

/-! ## sorting -/

lemma dirLe_total (p q : DirPt) : dirLe p q = true ∨ dirLe q p = true := by
  obtain ⟨t1, b1, _, _⟩ := p
  obtain ⟨t2, b2, _, _⟩ := q
  cases b1 <;> cases b2 <;> simp [dirLe, le_total]

lemma dirLe_trans {p q r : DirPt} (h1 : dirLe p q = true) (h2 : dirLe q r = true) : dirLe p r = true := by
  obtain ⟨t1, b1, _, _⟩ := p
  obtain ⟨t2, b2, _, _⟩ := q
  obtain ⟨t3, b3, _, _⟩ := r
  cases b1 <;> cases b2 <;> cases b3 <;> simp_all [dirLe] <;> omega

lemma mem_insertSorted {p x : DirPt} : ∀ {l : List DirPt}, x ∈ insertSorted p l ↔ x = p ∨ x ∈ l
  | [] => by simp [insertSorted]
  | q :: qs => by
    unfold insertSorted
    split_ifs
    · simp
    · simp only [List.mem_cons]; rw [mem_insertSorted]; tauto

lemma insertSorted_pairwise {p : DirPt} : ∀ {l : List DirPt}, l.Pairwise (fun a b => dirLe a b = true) →
    (insertSorted p l).Pairwise (fun a b => dirLe a b = true)
  | [], _ => by simp [insertSorted]
  | q :: qs, h => by
    unfold insertSorted
    split_ifs with hpq
    · refine List.Pairwise.cons ?_ h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hpq
      · exact dirLe_trans hpq (List.rel_of_pairwise_cons h hx)
    · have hqp : dirLe q p = true := (dirLe_total p q).resolve_left hpq
      refine List.Pairwise.cons ?_ (insertSorted_pairwise h.of_cons)
      intro x hx
      rcases mem_insertSorted.mp hx with rfl | hx
      · exact hqp
      · exact List.rel_of_pairwise_cons h hx

lemma mem_sortDirs {x : DirPt} : ∀ {l : List DirPt}, x ∈ sortDirs l ↔ x ∈ l
  | [] => by simp [sortDirs]
  | p :: ps => by simp only [sortDirs, mem_insertSorted, mem_sortDirs, List.mem_cons]

lemma sortDirs_pairwise : ∀ (l : List DirPt), (sortDirs l).Pairwise (fun a b => dirLe a b = true)
  | [] => by simp [sortDirs]
  | _ :: ps => insertSorted_pairwise (sortDirs_pairwise ps)

/-! ## the uncovered set -/

/-- the union of the uncovered elementary intervals `[p, q)` of consecutive points -/
def uSet (PS : List Piece) : List DirPt → Set ℝ
  | p :: q :: rest => (if covered PS p q = true then ∅ else Ico (dval p) (dval q)) ∪ uSet PS (q :: rest)
  | _ => ∅

lemma uSet_cons_cons (PS : List Piece) (p q : DirPt) (rest : List DirPt) :
    uSet PS (p :: q :: rest) =
      (if covered PS p q = true then ∅ else Ico (dval p) (dval q)) ∪ uSet PS (q :: rest) := rfl

lemma uSet_measurable (PS : List Piece) : ∀ (L : List DirPt), MeasurableSet (uSet PS L)
  | [] => MeasurableSet.empty
  | [_] => MeasurableSet.empty
  | p :: q :: rest => by
    rw [uSet_cons_cons]
    refine MeasurableSet.union ?_ (uSet_measurable PS (q :: rest))
    split_ifs
    · exact MeasurableSet.empty
    · exact measurableSet_Ico

lemma uSet_subset (PS : List Piece) : ∀ (L : List DirPt), (∀ p ∈ L, 0 ≤ dval p ∧ dval p ≤ 2 * π) →
    uSet PS L ⊆ Icc 0 (2 * π)
  | [], _ => by simp [uSet]
  | [_], _ => by simp [uSet]
  | p :: q :: rest, h => by
    rw [uSet_cons_cons]
    refine union_subset ?_ (uSet_subset PS (q :: rest) fun x hx => h x (List.mem_cons_of_mem _ hx))
    split_ifs
    · exact empty_subset _
    · intro t ht
      have hp := h p (by simp)
      have hq := h q (by simp)
      exact ⟨le_trans hp.1 ht.1, le_trans ht.2.le hq.2⟩

lemma uSet_ge (PS : List Piece) : ∀ (L : List DirPt) (q : DirPt),
    (q :: L).Pairwise (fun a b => dval a ≤ dval b) → uSet PS (q :: L) ⊆ Ici (dval q)
  | [], _, _ => by simp [uSet]
  | r :: rest, q, h => by
    rw [uSet_cons_cons]
    refine union_subset ?_ ?_
    · split_ifs
      · exact empty_subset _
      · exact fun t ht => ht.1
    · have hqr : dval q ≤ dval r := List.rel_of_pairwise_cons h (by simp)
      exact fun t ht => le_trans hqr (uSet_ge PS rest r h.of_cons ht)

/-! ## the integrals -/

/-- the integrand of the area: `(ρ² + ρ (cx cos t + cy sin t)) / 2` -/
def fA (ρ cx cy : ℝ) (t : ℝ) : ℝ := (ρ ^ 2 + ρ * (cx * Real.cos t + cy * Real.sin t)) / 2

lemma fA_continuous (ρ cx cy : ℝ) : Continuous (fA ρ cx cy) := by unfold fA; fun_prop

lemma integral_fA (ρ cx cy a b : ℝ) :
    ∫ t in a..b, fA ρ cx cy t
      = (ρ ^ 2 * (b - a) + ρ * (cx * (Real.sin b - Real.sin a) + cy * (Real.cos a - Real.cos b))) / 2 := by
  have hF : ∀ x ∈ uIcc a b, HasDerivAt (fun t => (ρ ^ 2 * t + ρ * (cx * Real.sin t - cy * Real.cos t)) / 2)
      (fA ρ cx cy x) x := by
    intro x _
    have h1 := ((((Real.hasDerivAt_sin x).const_mul cx).sub ((Real.hasDerivAt_cos x).const_mul cy)).const_mul ρ)
    have h2 := ((hasDerivAt_id x).const_mul (ρ ^ 2)).add h1
    have h3 := h2.div_const 2
    convert h3 using 1
    · funext t; simp
    · simp only [fA, id]; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF ((fA_continuous ρ cx cy).intervalIntegrable a b)]
  ring

lemma setIntegral_Ico_eq {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    ∫ t in Ico a b, f t = ∫ t in a..b, f t := by
  rw [intervalIntegral.integral_of_le hab, integral_Ico_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]

lemma dirVal_mem (p : DirPt) : ivMem (dval p) (dirVal p) := by
  unfold dirVal
  cases h : p.top
  · simp only [Bool.false_eq_true, ite_false]
    rw [dval_of_not_top h]; exact Iv.mem_pt p.t
  · simp only [ite_true]
    rw [dval_top h]
    have h1 := pL_lt_pi
    have h2 := pi_lt_pH
    have hS := SC_pos
    unfold ivMem; simp only; push_cast
    constructor
    · have : (piLo : ℝ) < π * SC := by rwa [div_lt_iff₀ hS] at h1
      show 2 * (piLo : ℝ) ≤ 2 * π * 2 ^ PR
      have e : (2 : ℝ) ^ PR = SC := rfl
      rw [e]; linarith
    · have : π * SC < (piHi : ℝ) := by rwa [lt_div_iff₀ hS] at h2
      show 2 * π * 2 ^ PR ≤ 2 * (piHi : ℝ)
      have e : (2 : ℝ) ^ PR = SC := rfl
      rw [e]; linarith

lemma elemInt_spec (R cx cy : ℤ) {p q : DirPt} (hp : DirOK p) (hq : DirOK q) :
    ivMem (∫ t in dval p..dval q, fA (fx R) (fx cx) (fx cy) t) (elemInt R cx cy p q).1 ∧
    ivMem (Real.sin (dval q) - Real.sin (dval p)) (elemInt R cx cy p q).2.1 ∧
    ivMem (Real.cos (dval p) - Real.cos (dval q)) (elemInt R cx cy p q).2.2 := by
  have hlen := Iv.mem_sub (dirVal_mem q) (dirVal_mem p)
  have hds := Iv.mem_sub hq.2 hp.2
  have hdc := Iv.mem_sub hp.1 hq.1
  have hR2 := Iv.mem_sqr (Iv.mem_pt R)
  have ha := Iv.mem_add (Iv.mem_mul hR2 hlen) (Iv.mem_mul (Iv.mem_pt R)
    (Iv.mem_add (Iv.mem_mul (Iv.mem_pt cx) hds) (Iv.mem_mul (Iv.mem_pt cy) hdc)))
  have h2 := Iv.mem_div2e ha 1
  refine ⟨?_, hds, hdc⟩
  rw [integral_fA]
  simpa [elemInt] using h2

lemma integral_empty' (f : ℝ → ℝ) : ∫ t in (∅ : Set ℝ), f t = 0 := by simp

lemma mem_int_zero : ivMem 0 (Iv.int 0) := by
  have h0 := Iv.mem_int 0; rwa [Int.cast_zero] at h0

/-- `sumElems` encloses the integrals over the uncovered set. -/
theorem sumElems_spec (R cx cy : ℤ) (PS : List Piece) : ∀ (L : List DirPt),
    L.Pairwise (fun p q => dval p ≤ dval q) → (∀ p ∈ L, DirOK p ∧ 0 ≤ dval p ∧ dval p ≤ 2 * π) →
    ivMem (∫ t in uSet PS L, fA (fx R) (fx cx) (fx cy) t) (sumElems R cx cy PS L).1 ∧
    ivMem (∫ t in uSet PS L, Real.cos t) (sumElems R cx cy PS L).2.1 ∧
    ivMem (∫ t in uSet PS L, Real.sin t) (sumElems R cx cy PS L).2.2
  | [], _, _ => by
    simp only [uSet, sumElems, integral_empty']; exact ⟨mem_int_zero, mem_int_zero, mem_int_zero⟩
  | [_], _, _ => by
    simp only [uSet, sumElems, integral_empty']; exact ⟨mem_int_zero, mem_int_zero, mem_int_zero⟩
  | p :: q :: rest, hs, hok => by
    have ih := sumElems_spec R cx cy PS (q :: rest) hs.of_cons
      (fun x hx => hok x (List.mem_cons_of_mem _ hx))
    have hpq : dval p ≤ dval q := List.rel_of_pairwise_cons hs (by simp)
    have hpok := hok p (by simp)
    have hqok := hok q (by simp)
    rcases hrec : sumElems R cx cy PS (q :: rest) with ⟨a, gx, gy⟩
    rw [hrec] at ih
    simp only [sumElems, hrec, uSet_cons_cons]
    split_ifs with hc
    · simpa using ih
    · -- the union of `[p, q)` and the rest
      have hsub : uSet PS (q :: rest) ⊆ Icc 0 (2 * π) :=
        uSet_subset PS (q :: rest) fun x hx => (hok x (List.mem_cons_of_mem _ hx)).2
      have hdisj : Disjoint (Ico (dval p) (dval q)) (uSet PS (q :: rest)) := by
        rw [Set.disjoint_left]
        intro t ht ht'
        have := uSet_ge PS rest q hs.of_cons ht'
        exact absurd ht.2 (not_lt.mpr this)
      have hIco : Ico (dval p) (dval q) ⊆ Icc 0 (2 * π) := fun t ht =>
        ⟨le_trans hpok.2.1 ht.1, le_trans ht.2.le hqok.2.2⟩
      have hm := uSet_measurable PS (q :: rest)
      have key : ∀ f : ℝ → ℝ, Continuous f →
          ∫ t in Ico (dval p) (dval q) ∪ uSet PS (q :: rest), f t
            = (∫ t in dval p..dval q, f t) + ∫ t in uSet PS (q :: rest), f t := by
        intro f hf
        rw [setIntegral_union hdisj hm (hf.integrableOn_Icc.mono_set hIco) (hf.integrableOn_Icc.mono_set hsub),
          setIntegral_Ico_eq hpq]
      obtain ⟨e1, e2, e3⟩ := elemInt_spec R cx cy hpok.1 hqok.1
      rw [key _ (fA_continuous _ _ _), key _ Real.continuous_cos, key _ Real.continuous_sin,
        integral_cos, integral_sin]
      refine ⟨?_, ?_, ?_⟩
      · rw [add_comm]; exact Iv.mem_add ih.1 e1
      · rw [add_comm]; exact Iv.mem_add ih.2.1 e2
      · rw [add_comm]; exact Iv.mem_add ih.2.2 e3

/-! ## the uncovered set versus the pieces -/

/-- a point of `uSet` lies in an uncovered elementary interval `[p, q)` of points of `L`, and every point of `L`
is `≤ p` or `≥ q` -/
lemma uSet_avoid (PS : List Piece) : ∀ (L : List DirPt), L.Pairwise (fun p q => dval p ≤ dval q) →
    ∀ t ∈ uSet PS L, ∃ p q, p ∈ L ∧ q ∈ L ∧ covered PS p q = false ∧ t ∈ Ico (dval p) (dval q) ∧
      ∀ x ∈ L, dval x ≤ dval p ∨ dval q ≤ dval x
  | [], _, t, ht => by simp [uSet] at ht
  | [_], _, t, ht => by simp [uSet] at ht
  | p :: q :: rest, hs, t, ht => by
    rw [uSet_cons_cons] at ht
    rcases ht with ht | ht
    · split_ifs at ht with hc
      · exact absurd ht (notMem_empty t)
      · refine ⟨p, q, by simp, by simp, by simpa using hc, ht, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · left; exact le_refl _
        · right
          rcases List.mem_cons.mp hx with rfl | hx
          · exact le_refl _
          · exact List.rel_of_pairwise_cons hs.of_cons hx
    · obtain ⟨p', q', hp', hq', hc, ht', hx⟩ := uSet_avoid PS (q :: rest) hs.of_cons t ht
      refine ⟨p', q', List.mem_cons_of_mem _ hp', List.mem_cons_of_mem _ hq', hc, ht', ?_⟩
      intro x hxL
      rcases List.mem_cons.mp hxL with rfl | hxL
      · left; exact List.rel_of_pairwise_cons hs hp'
      · exact hx x hxL

/-- `uSet` meets no open piece whose endpoint values occur in `L` -/
theorem uSet_avoid_pieces (PS : List Piece) (L : List DirPt) (hs : L.Pairwise (fun p q => dval p ≤ dval q))
    (hL : ∀ p ∈ L, InRange p) {t : ℝ} (ht : t ∈ uSet PS L) {pc : Piece} (hpc : pc ∈ PS)
    (ha : InRange pc.a) (hb : InRange pc.b) (ha' : ∃ x ∈ L, dval x = dval pc.a)
    (hb' : ∃ y ∈ L, dval y = dval pc.b) : t ∉ Ioo (dval pc.a) (dval pc.b) := by
  intro htab
  obtain ⟨p, q, hp, hq, hc, htpq, hx⟩ := uSet_avoid PS L hs t ht
  obtain ⟨x, hxL, hxa⟩ := ha'
  obtain ⟨y, hyL, hyb⟩ := hb'
  have h1 : dval pc.a ≤ dval p := by
    rcases hx x hxL with h | h
    · rw [← hxa]; exact h
    · exfalso; rw [hxa] at h; linarith [htab.1, htpq.2]
  have h2 : dval q ≤ dval pc.b := by
    rcases hx y hyL with h | h
    · exfalso; rw [hyb] at h; linarith [htab.2, htpq.1]
    · rw [← hyb]; exact h
  have hcov : covered PS p q = true := by
    unfold covered
    rw [List.any_eq_true]
    refine ⟨pc, hpc, ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨(dirLe_iff ha (hL p hp)).mpr h1, (dirLe_iff (hL q hq) hb).mpr h2⟩
  rw [hc] at hcov
  exact absurd hcov (by decide)

/-- a point between the first and the last point of `L` that is not in `uSet` lies in a closed piece -/
theorem uSet_cover (PS : List Piece) (hPS : ∀ pc ∈ PS, InRange pc.a ∧ InRange pc.b) : ∀ (L : List DirPt),
    L.Pairwise (fun p q => dval p ≤ dval q) → (∀ p ∈ L, InRange p) → ∀ t : ℝ,
    (∃ x ∈ L, dval x ≤ t) → (∃ y ∈ L, t < dval y) → t ∉ uSet PS L →
    ∃ pc ∈ PS, t ∈ Icc (dval pc.a) (dval pc.b)
  | [], _, _, t, ⟨x, hx, _⟩, _, _ => by simp at hx
  | [p], _, _, t, ⟨x, hx, hxt⟩, ⟨y, hy, hyt⟩, _ => by
    simp only [List.mem_singleton] at hx hy
    subst hx; subst hy; linarith
  | p :: q :: rest, hs, hL, t, ⟨x, hx, hxt⟩, ⟨y, hy, hyt⟩, hnot => by
    rw [uSet_cons_cons] at hnot
    rcases lt_or_ge t (dval q) with htq | htq
    · have hpt : dval p ≤ t := by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hxt
        · have : dval q ≤ dval x := by
            rcases List.mem_cons.mp hx with rfl | hx
            · exact le_refl _
            · exact List.rel_of_pairwise_cons hs.of_cons hx
          linarith
      by_cases hc : covered PS p q = true
      · unfold covered at hc
        rw [List.any_eq_true] at hc
        obtain ⟨pc, hpc, hpc'⟩ := hc
        rw [Bool.and_eq_true] at hpc'
        have h1 := (dirLe_iff (hPS pc hpc).1 (hL p (by simp))).mp hpc'.1
        have h2 := (dirLe_iff (hL q (by simp)) (hPS pc hpc).2).mp hpc'.2
        exact ⟨pc, hpc, by linarith, by linarith⟩
      · exfalso
        apply hnot
        left
        rw [if_neg hc]
        exact ⟨hpt, htq⟩
    · have hy' : y ∈ q :: rest := by
        rcases List.mem_cons.mp hy with rfl | hy
        · exfalso
          have : dval y ≤ dval q := List.rel_of_pairwise_cons hs (by simp)
          linarith
        · exact hy
      exact uSet_cover PS hPS (q :: rest) hs.of_cons (fun z hz => hL z (List.mem_cons_of_mem _ hz)) t
        ⟨q, by simp, htq⟩ ⟨y, hy', hyt⟩ (fun h => hnot (Or.inr h))

end US

end

end BHH
