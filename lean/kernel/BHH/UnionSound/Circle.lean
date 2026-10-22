/-
Module B (union area), part 5: one circle.

`circleInt_spec`: if every arc of the list is a proxy (`ArcFor`) of its covered set, `circleInt` encloses the
integrals of the area integrand `(ρ² + ρ⟨c, u(t)⟩)/2`, of `cos` and of `sin` over the exposed set
`[0, 2π) \ ⋃ (covered sets)`.  Proof: the code integrates exactly (with interval arithmetic) over the uncovered set
`E'` of the sweep; `E Δ E'` lies in `{0}` and the mod-`2π` images of the `U \ I`, of measure `≤ Σ slack`; and
`|∫_E f - ∫_E' f| ≤ sup |f| · Σ slack`.
-/
import BHH.UnionSound.Measure

open BHH.Cert Real Set MeasureTheory

namespace BHH

noncomputable section

namespace US

/-! ## the lists built by `circleInt` -/

/-- the pieces of a list of arcs -/
def piecesOf (arcs : List Arc) : List Piece := arcs.foldr (fun ar acc => normArc ar.s ar.e ++ acc) []

lemma piecesOf_cons (ar : Arc) (arcs : List Arc) : piecesOf (ar :: arcs) = normArc ar.s ar.e ++ piecesOf arcs :=
  rfl

lemma mem_piecesOf {pc : Piece} : ∀ {arcs : List Arc}, pc ∈ piecesOf arcs ↔ ∃ ar ∈ arcs, pc ∈ normArc ar.s ar.e
  | [] => by simp [piecesOf]
  | ar :: arcs => by
    rw [piecesOf_cons, List.mem_append, mem_piecesOf]
    simp only [List.mem_cons, exists_eq_or_imp]

/-- the non-top endpoints of the pieces -/
def endsOf (PS : List Piece) : List DirPt :=
  PS.foldr (fun pc acc => (if pc.a.top then acc else pc.a :: (if pc.b.top then acc else pc.b :: acc))) []

lemma endsOf_cons (pc : Piece) (PS : List Piece) : endsOf (pc :: PS) =
    (if pc.a.top then endsOf PS else pc.a :: (if pc.b.top then endsOf PS else pc.b :: endsOf PS)) := rfl

lemma mem_endsOf {x : DirPt} : ∀ {PS : List Piece}, x ∈ endsOf PS → ∃ pc ∈ PS, x = pc.a ∨ x = pc.b
  | [], h => by simp [endsOf] at h
  | pc :: PS, h => by
    rw [endsOf_cons] at h
    have ih : x ∈ endsOf PS → ∃ pc' ∈ pc :: PS, x = pc'.a ∨ x = pc'.b := fun h' => by
      obtain ⟨pc', hpc', hx⟩ := mem_endsOf h'
      exact ⟨pc', List.mem_cons_of_mem _ hpc', hx⟩
    split_ifs at h
    · exact ih h
    · rcases List.mem_cons.mp h with rfl | h
      · exact ⟨pc, by simp, Or.inl rfl⟩
      · exact ih h
    · rcases List.mem_cons.mp h with rfl | h
      · exact ⟨pc, by simp, Or.inl rfl⟩
      · rcases List.mem_cons.mp h with rfl | h
        · exact ⟨pc, by simp, Or.inr rfl⟩
        · exact ih h

lemma endsOf_mono {x : DirPt} {pc : Piece} {PS : List Piece} (h : x ∈ endsOf PS) : x ∈ endsOf (pc :: PS) := by
  rw [endsOf_cons]
  split_ifs
  · exact h
  · exact List.mem_cons_of_mem _ h
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

lemma endsOf_a {pc : Piece} : ∀ {PS : List Piece}, pc ∈ PS → pc.a.top = false → pc.a ∈ endsOf PS
  | [], h, _ => by simp at h
  | q :: PS, h, ha => by
    rcases List.mem_cons.mp h with rfl | h
    · rw [endsOf_cons, if_neg (by simp [ha])]; exact List.mem_cons_self
    · exact endsOf_mono (endsOf_a h ha)

lemma endsOf_b {pc : Piece} : ∀ {PS : List Piece}, pc ∈ PS → pc.a.top = false → pc.b.top = false →
    pc.b ∈ endsOf PS
  | [], h, _, _ => by simp at h
  | q :: PS, h, ha, hb => by
    rcases List.mem_cons.mp h with rfl | h
    · rw [endsOf_cons, if_neg (by simp [ha]), if_neg (by simp [hb])]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact endsOf_mono (endsOf_b h ha hb)

/-- the total slack of a list of arcs -/
def slackOf (arcs : List Arc) : ℤ := arcs.foldr (fun ar acc => ar.slack + acc) 0

lemma fx_slackOf (L : List (Arc × Set ℝ)) : fx (slackOf (L.map Prod.fst)) = (L.map fun p => fx p.1.slack).sum := by
  induction L with
  | nil => simp [slackOf, fx_zero]
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih]
    show fx (p.1.slack + slackOf (L.map Prod.fst)) = _
    rw [fx_add]

lemma circleInt_eq (R cx cy : ℤ) (arcs : List Arc) : circleInt R cx cy arcs =
    (Iv.widen (sumElems R cx cy (piecesOf arcs) (sortDirs (dirZero :: endsOf (piecesOf arcs)) ++ [dirTop])).1
        (shrU ((shrU (R * R + R * (cx.natAbs + cy.natAbs : ℤ)) (PR + 1) + 1) * max (slackOf arcs) 0) PR + 1),
      Iv.widen (sumElems R cx cy (piecesOf arcs) (sortDirs (dirZero :: endsOf (piecesOf arcs)) ++ [dirTop])).2.1
        (max (slackOf arcs) 0),
      Iv.widen (sumElems R cx cy (piecesOf arcs) (sortDirs (dirZero :: endsOf (piecesOf arcs)) ++ [dirTop])).2.2
        (max (slackOf arcs) 0)) := rfl

/-! ## small lemmas -/

lemma list_sum_map_le_real {α : Type*} (L : List α) (f g : α → ℝ) (h : ∀ p ∈ L, f p ≤ g p) :
    (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a (by simp)) (ih fun p hp => h p (List.mem_cons_of_mem _ hp))

lemma list_sum_map_le_ennreal {α : Type*} (L : List α) (f g : α → ENNReal) (h : ∀ p ∈ L, f p ≤ g p) :
    (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a (by simp)) (ih fun p hp => h p (List.mem_cons_of_mem _ hp))

lemma int_eq_zero_of_bounds {k : ℤ} (h1 : -(2 * π) < k * (2 * π)) (h2 : k * (2 * π) < 2 * π) : k = 0 := by
  have hπ : 0 < 2 * π := Real.two_pi_pos
  have a1 : (-1 : ℝ) < k := by
    by_contra h; push Not at h; nlinarith
  have a2 : (k : ℝ) < 1 := by
    by_contra h; push Not at h; nlinarith
  have b1 : -1 < k := by exact_mod_cast a1
  have b2 : k < 1 := by exact_mod_cast a2
  omega

lemma uSet_subset_Ico (PS : List Piece) : ∀ (L : List DirPt), (∀ p ∈ L, 0 ≤ dval p ∧ dval p ≤ 2 * π) →
    uSet PS L ⊆ Ico 0 (2 * π)
  | [], _ => by simp [uSet]
  | [_], _ => by simp [uSet]
  | p :: q :: rest, h => by
    rw [uSet_cons_cons]
    refine union_subset ?_ (uSet_subset_Ico PS (q :: rest) fun x hx => h x (List.mem_cons_of_mem _ hx))
    split_ifs
    · exact empty_subset _
    · intro t ht
      have hp := h p (by simp)
      have hq := h q (by simp)
      exact ⟨le_trans hp.1 ht.1, lt_of_lt_of_le ht.2 hq.2⟩

/-- the exposed set of a circle with the covered sets `p.2`, `p ∈ L` -/
def expSet (L : List (Arc × Set ℝ)) : Set ℝ := {t | t ∈ Ico 0 (2 * π) ∧ ∀ p ∈ L, t ∉ p.2}

lemma measurableSet_expSet : ∀ (L : List (Arc × Set ℝ)), (∀ p ∈ L, MeasurableSet p.2) → MeasurableSet (expSet L)
  | [], _ => by
    have : expSet [] = Ico 0 (2 * π) := by ext t; simp [expSet]
    rw [this]; exact measurableSet_Ico
  | p :: L, h => by
    have : expSet (p :: L) = expSet L ∩ p.2ᶜ := by
      ext t; simp only [expSet, List.mem_cons, forall_eq_or_imp, mem_setOf_eq, mem_inter_iff, mem_compl_iff]
      tauto
    rw [this]
    exact (measurableSet_expSet L fun q hq => h q (List.mem_cons_of_mem _ hq)).inter (h p (by simp)).compl

lemma abs_fA_le (ρ cx cy t : ℝ) (hρ : 0 ≤ ρ) :
    |fA ρ cx cy t| ≤ (ρ ^ 2 + ρ * (|cx| + |cy|)) / 2 := by
  unfold fA
  have hc := Real.abs_cos_le_one t
  have hs := Real.abs_sin_le_one t
  have h1 : |cx * Real.cos t + cy * Real.sin t| ≤ |cx| + |cy| := by
    calc |cx * Real.cos t + cy * Real.sin t| ≤ |cx * Real.cos t| + |cy * Real.sin t| := abs_add_le _ _
      _ = |cx| * |Real.cos t| + |cy| * |Real.sin t| := by rw [abs_mul, abs_mul]
      _ ≤ |cx| * 1 + |cy| * 1 := by gcongr
      _ = |cx| + |cy| := by ring
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  gcongr
  calc |ρ ^ 2 + ρ * (cx * Real.cos t + cy * Real.sin t)| ≤ |ρ ^ 2| + |ρ * (cx * Real.cos t + cy * Real.sin t)| :=
        abs_add_le _ _
    _ = ρ ^ 2 + ρ * |cx * Real.cos t + cy * Real.sin t| := by
        rw [abs_mul, abs_of_nonneg hρ, abs_of_nonneg (sq_nonneg ρ)]
    _ ≤ ρ ^ 2 + ρ * (|cx| + |cy|) := by gcongr

/-- the bound `sup |fA| · S ≤ errA / 2^PR` of the area widening -/
lemma errA_bound (R cx cy sl : ℤ) (hR : 0 ≤ R) {S : ℝ} (hS0 : 0 ≤ S) (hsl : S * SC ≤ sl) :
    (fx R ^ 2 + fx R * (|fx cx| + |fx cy|)) / 2 * S
      ≤ fx (shrU ((shrU (R * R + R * (cx.natAbs + cy.natAbs : ℤ)) (PR + 1) + 1) * sl) PR + 1) := by
  have hSC := SC_pos
  set M := (fx R ^ 2 + fx R * (|fx cx| + |fx cy|)) / 2 with hM
  have hρ : 0 ≤ fx R := fx_nonneg_iff.mpr hR
  have hM0 : 0 ≤ M := by positivity
  -- supf ≥ M · SC
  have hsup : M * SC ≤ ((shrU (R * R + R * (cx.natAbs + cy.natAbs : ℤ)) (PR + 1) + 1 : ℤ) : ℝ) := by
    have h := le_shrU (R * R + R * (cx.natAbs + cy.natAbs : ℤ)) (PR + 1)
    rw [two_pow_PR_succ] at h
    push_cast at h ⊢
    have e1 : ((cx.natAbs : ℤ) : ℝ) = |(cx : ℝ)| := by rw [Int.natCast_natAbs, Int.cast_abs]
    have e2 : ((cy.natAbs : ℤ) : ℝ) = |(cy : ℝ)| := by rw [Int.natCast_natAbs, Int.cast_abs]
    try simp only [Nat.cast_natAbs, Int.cast_abs, e1, e2] at h
    have e3 : M * SC = ((R : ℝ) * R + R * (|(cx : ℝ)| + |(cy : ℝ)|)) / (2 * SC) := by
      rw [hM]; simp only [fx_eq, abs_div, abs_of_pos hSC]; field_simp
    rw [e3]; linarith
  have hsl0 : 0 ≤ (sl : ℝ) := le_trans (mul_nonneg hS0 hSC.le) hsl
  have hprod : M * SC * (S * SC) ≤ ((shrU (R * R + R * (cx.natAbs + cy.natAbs : ℤ)) (PR + 1) + 1 : ℤ) : ℝ) * sl :=
    mul_le_mul hsup hsl (by positivity) (le_trans (by positivity) hsup)
  have h2 := le_shrU ((shrU (R * R + R * (cx.natAbs + cy.natAbs : ℤ)) (PR + 1) + 1) * sl) PR
  rw [fx_eq]
  rw [le_div_iff₀ hSC]
  push_cast at h2 ⊢
  have e : (2 : ℝ) ^ PR = SC := rfl
  rw [e] at h2
  have : M * S * SC = M * SC * (S * SC) / SC := by field_simp
  rw [this]
  have : M * SC * (S * SC) / SC ≤
      ((shrU (R * R + R * (cx.natAbs + cy.natAbs : ℤ)) (PR + 1) + 1 : ℤ) : ℝ) * sl / SC :=
    div_le_div_of_nonneg_right (by exact_mod_cast hprod) hSC.le
  push_cast at this
  linarith

/-! ## the theorem for one circle -/

theorem circleInt_spec (R cx cy : ℤ) (hR : 0 ≤ R) (L : List (Arc × Set ℝ)) (hL : ∀ p ∈ L, ArcFor p.2 p.1) :
    ivMem (∫ t in expSet L, fA (fx R) (fx cx) (fx cy) t) (circleInt R cx cy (L.map Prod.fst)).1 ∧
    ivMem (∫ t in expSet L, Real.cos t) (circleInt R cx cy (L.map Prod.fst)).2.1 ∧
    ivMem (∫ t in expSet L, Real.sin t) (circleInt R cx cy (L.map Prod.fst)).2.2 := by
  classical
  set arcs := L.map Prod.fst with harcs
  set PS := piecesOf arcs with hPS
  set pts := dirZero :: endsOf PS with hpts
  set srt := sortDirs pts ++ [dirTop] with hsrt
  have hmeasA : ∀ p ∈ L, MeasurableSet p.2 := fun p hp => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩ := hL p hp
    exact hm
  choose! fa fc fd fb hdata using hL
  -- pieces
  have hPSprop : ∀ pc ∈ PS, ∃ p ∈ L, pc ∈ normArc p.1.s p.1.e := by
    intro pc hpc
    obtain ⟨ar, har, hpc'⟩ := mem_piecesOf.mp hpc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp har
    exact ⟨p, hp, hpc'⟩
  have hN : ∀ p ∈ L,
      (∀ pc ∈ normArc p.1.s p.1.e, pc.a.top = false ∧ InRange pc.a ∧ InRange pc.b ∧ DirOK pc.a ∧ DirOK pc.b) ∧
      (∀ pc ∈ normArc p.1.s p.1.e, ∀ t ∈ Icc (dval pc.a) (dval pc.b),
        ∃ n : ℤ, t + n * (2 * π) ∈ Ioo (fa p) (fb p)) ∧
      (∀ x ∈ Icc (fc p) (fd p), (∃ m : ℤ, x + m * (2 * π) = 0) ∨
        ∃ pc ∈ normArc p.1.s p.1.e, ∃ m : ℤ, x + m * (2 * π) ∈ Ioo (dval pc.a) (dval pc.b)) := by
    intro p hp
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -, -, -, -, -⟩ := hdata p hp
    exact normArc_spec h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  have hPS1 : ∀ pc ∈ PS, pc.a.top = false ∧ InRange pc.a ∧ InRange pc.b ∧ DirOK pc.a ∧ DirOK pc.b := by
    intro pc hpc
    obtain ⟨p, hp, hpc'⟩ := hPSprop pc hpc
    exact (hN p hp).1 pc hpc'
  -- the sorted points
  have hpts1 : ∀ x ∈ pts, InRange x ∧ DirOK x := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨InRange_dirZero, DirOK_dirZero⟩
    · obtain ⟨pc, hpc, rfl | rfl⟩ := mem_endsOf hx
      · exact ⟨(hPS1 pc hpc).2.1, (hPS1 pc hpc).2.2.2.1⟩
      · exact ⟨(hPS1 pc hpc).2.2.1, (hPS1 pc hpc).2.2.2.2⟩
  have hsrt1 : ∀ x ∈ srt, InRange x ∧ DirOK x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hpts1 x (mem_sortDirs.mp hx)
    · rw [List.mem_singleton] at hx; subst hx; exact ⟨InRange_dirTop, DirOK_dirTop⟩
  have hsrt2 : ∀ x ∈ srt, 0 ≤ dval x ∧ dval x ≤ 2 * π := fun x hx => dval_mem (hsrt1 x hx).1
  have hsorted : srt.Pairwise (fun p q => dval p ≤ dval q) := by
    rw [hsrt, List.pairwise_append]
    refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
    · exact (sortDirs_pairwise pts).imp_of_mem (fun {a b} ha hb h =>
        (dirLe_iff (hpts1 a (mem_sortDirs.mp ha)).1 (hpts1 b (mem_sortDirs.mp hb)).1).mp h)
    · intro a ha b hb
      rw [List.mem_singleton] at hb; subst hb
      rw [dval_dirTop]; exact (dval_mem (hpts1 a (mem_sortDirs.mp ha)).1).2
  have hzero_mem : dirZero ∈ srt := List.mem_append_left _ (mem_sortDirs.mpr List.mem_cons_self)
  have htop_mem : dirTop ∈ srt := List.mem_append_right _ (List.mem_singleton_self _)
  have ha_mem : ∀ pc ∈ PS, ∃ x ∈ srt, dval x = dval pc.a := fun pc hpc =>
    ⟨pc.a, List.mem_append_left _ (mem_sortDirs.mpr (List.mem_cons_of_mem _ (endsOf_a hpc (hPS1 pc hpc).1))), rfl⟩
  have hb_mem : ∀ pc ∈ PS, ∃ y ∈ srt, dval y = dval pc.b := by
    intro pc hpc
    cases hb : pc.b.top
    · exact ⟨pc.b, List.mem_append_left _ (mem_sortDirs.mpr (List.mem_cons_of_mem _
        (endsOf_b hpc (hPS1 pc hpc).1 hb))), rfl⟩
    · exact ⟨dirTop, htop_mem, by rw [dval_dirTop, dval_top hb]⟩
  -- the sweep
  have hsw := sumElems_spec R cx cy PS srt hsorted (fun x hx => ⟨(hsrt1 x hx).2, hsrt2 x hx⟩)
  set E' := uSet PS srt with hE'
  set E := expSet L with hE
  have hE'm : MeasurableSet E' := uSet_measurable PS srt
  have hEm : MeasurableSet E := measurableSet_expSet L hmeasA
  have hE'b : E' ⊆ Icc 0 (2 * π) := uSet_subset PS srt hsrt2
  have hEb : E ⊆ Icc 0 (2 * π) := fun t ht => Ico_subset_Icc_self ht.1
  -- the symmetric difference
  have hincl : (E \ E') ∪ (E' \ E) ⊆ {0} ∪ ⋃ p ∈ L, modSet (Ioo (fa p) (fb p) \ Icc (fc p) (fd p)) := by
    rintro t (⟨⟨htI, htL⟩, htE'⟩ | ⟨htE', htE⟩)
    · right
      obtain ⟨pc, hpc, htpc⟩ := uSet_cover PS (fun pc hpc => ⟨(hPS1 pc hpc).2.1, (hPS1 pc hpc).2.2.1⟩) srt
        hsorted (fun x hx => (hsrt1 x hx).1) t ⟨dirZero, hzero_mem, by rw [dval_dirZero]; exact htI.1⟩
        ⟨dirTop, htop_mem, by rw [dval_dirTop]; exact htI.2⟩ htE'
      obtain ⟨p, hp, hpc'⟩ := hPSprop pc hpc
      obtain ⟨n, hn⟩ := (hN p hp).2.1 pc hpc' t htpc
      rw [mem_iUnion₂]
      refine ⟨p, hp, htI, n, hn, ?_⟩
      intro hI
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hIA, -, hper⟩ := hdata p hp
      have h1 := hper _ (-n) (hIA _ hI)
      rw [show t + n * (2 * π) + ((-n : ℤ) : ℝ) * (2 * π) = t by push_cast; ring] at h1
      exact htL p hp h1
    · have htI : t ∈ Ico 0 (2 * π) := uSet_subset_Ico PS srt hsrt2 htE'
      by_cases h0 : t = 0
      · left; exact h0
      right
      have hex : ∃ p ∈ L, t ∈ p.2 := by
        by_contra hcon
        push Not at hcon
        exact htE ⟨htI, hcon⟩
      obtain ⟨p, hp, htp⟩ := hex
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hU, -⟩ := hdata p hp
      obtain ⟨n, hn⟩ := hU t htp
      rw [mem_iUnion₂]
      refine ⟨p, hp, htI, n, hn, ?_⟩
      intro hI
      rcases (hN p hp).2.2 _ hI with ⟨m, hm⟩ | ⟨pc, hpc, m, hm⟩
      · apply h0
        have hk : ((n + m : ℤ) : ℝ) * (2 * π) = -t := by push_cast; linarith
        have : n + m = 0 := int_eq_zero_of_bounds (by rw [hk]; linarith [htI.2]) (by
          rw [hk]; linarith [htI.1, Real.two_pi_pos])
        rw [this] at hk; simp at hk; linarith
      · have hpcPS : pc ∈ PS := mem_piecesOf.mpr ⟨p.1, List.mem_map_of_mem hp, hpc⟩
        have hya := dval_mem (hPS1 pc hpcPS).2.1
        have hyb := dval_mem (hPS1 pc hpcPS).2.2.1
        have hk : n + m = 0 := by
          apply int_eq_zero_of_bounds
          · have : ((n + m : ℤ) : ℝ) * (2 * π) = (t + n * (2 * π) + m * (2 * π)) - t := by push_cast; ring
            rw [this]; linarith [hm.1, htI.2]
          · have : ((n + m : ℤ) : ℝ) * (2 * π) = (t + n * (2 * π) + m * (2 * π)) - t := by push_cast; ring
            rw [this]; linarith [hm.2, htI.1]
        have hy : t ∈ Ioo (dval pc.a) (dval pc.b) := by
          have : t = t + n * (2 * π) + m * (2 * π) := by
            have : (m : ℝ) = -n := by
              have : m = -n := by omega
              rw [this]; push_cast; ring
            rw [this]; ring
          rw [this]; exact hm
        exact uSet_avoid_pieces PS srt hsorted (fun x hx => (hsrt1 x hx).1) htE' hpcPS
          (hPS1 pc hpcPS).2.1 (hPS1 pc hpcPS).2.2.1 (ha_mem pc hpcPS) (hb_mem pc hpcPS) hy
  -- its measure
  have hterm : ∀ p ∈ L, 0 ≤ (fc p - fa p) + (fb p - fd p) ∧ (fc p - fa p) + (fb p - fd p) ≤ fx p.1.slack := by
    intro p hp
    obtain ⟨-, -, -, -, -, -, -, -, h9, h10, h11, h12, h13, -⟩ := hdata p hp
    have := pE_pos
    constructor
    · linarith
    · exact h13
  set S := fx (slackOf arcs) with hSdef
  have hSsum : S = (L.map fun p => fx p.1.slack).sum := fx_slackOf L
  have hS0 : 0 ≤ S := by
    rw [hSsum]
    exact List.sum_nonneg (fun x hx => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact le_trans (hterm p hp).1 (hterm p hp).2)
  have hvol : volume ((E \ E') ∪ (E' \ E)) ≤ ENNReal.ofReal S := by
    calc volume ((E \ E') ∪ (E' \ E))
        ≤ volume ({0} ∪ ⋃ p ∈ L, modSet (Ioo (fa p) (fb p) \ Icc (fc p) (fd p))) := measure_mono hincl
      _ ≤ volume ({0} : Set ℝ) + volume (⋃ p ∈ L, modSet (Ioo (fa p) (fb p) \ Icc (fc p) (fd p))) :=
          measure_union_le _ _
      _ = volume (⋃ p ∈ L, modSet (Ioo (fa p) (fb p) \ Icc (fc p) (fd p))) := by simp
      _ ≤ (L.map fun p => volume (modSet (Ioo (fa p) (fb p) \ Icc (fc p) (fd p)))).sum :=
          measure_list_biUnion_le L _
      _ ≤ (L.map fun p => ENNReal.ofReal ((fc p - fa p) + (fb p - fd p))).sum := by
          apply list_sum_map_le_ennreal
          intro p hp
          obtain ⟨-, -, -, -, -, -, -, -, h9, h10, h11, h12, -⟩ := hdata p hp
          have := pE_pos
          exact le_trans (volume_modSet_le _) (volume_Ioo_diff_Icc_le (by linarith) (by linarith))
      _ = ENNReal.ofReal (L.map fun p => (fc p - fa p) + (fb p - fd p)).sum :=
          list_sum_ofReal L _ (fun p hp => (hterm p hp).1)
      _ ≤ ENNReal.ofReal S := by
          apply ENNReal.ofReal_le_ofReal
          rw [hSsum]
          exact list_sum_map_le_real L _ _ (fun p hp => (hterm p hp).2)
  -- the three integrals
  have hρ : 0 ≤ fx R := fx_nonneg_iff.mpr hR
  have hM0 : 0 ≤ (fx R ^ 2 + fx R * (|fx cx| + |fx cy|)) / 2 := by positivity
  have dA := abs_setIntegral_sub_le (fA_continuous (fx R) (fx cx) (fx cy))
    (fun t => abs_fA_le (fx R) (fx cx) (fx cy) t hρ) hM0 hS0 hEm hE'm hEb hE'b hvol
  have dC := abs_setIntegral_sub_le Real.continuous_cos Real.abs_cos_le_one zero_le_one hS0 hEm hE'm hEb hE'b hvol
  have dS := abs_setIntegral_sub_le Real.continuous_sin Real.abs_sin_le_one zero_le_one hS0 hEm hE'm hEb hE'b hvol
  have hslS : S * SC ≤ ((max (slackOf arcs) 0 : ℤ) : ℝ) := by
    rw [hSdef, fx_mul_SC]; exact_mod_cast le_max_left _ _
  have hslfx : S ≤ fx (max (slackOf arcs) 0) := by
    rw [fx_eq, le_div_iff₀ SC_pos]; exact hslS
  rw [circleInt_eq]
  refine ⟨?_, ?_, ?_⟩
  · exact mem_widen_of_near hsw.1 (le_trans dA (errA_bound R cx cy _ hR hS0 hslS))
  · exact mem_widen_of_near hsw.2.1 (by linarith)
  · exact mem_widen_of_near hsw.2.2 (by linarith)

end US

end

end BHH
