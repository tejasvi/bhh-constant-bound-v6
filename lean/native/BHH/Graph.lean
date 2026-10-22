/-
The g table (module E, item 3): `GTabSound k gt` from the Bool check `checkTab` of `BHHCert/GTab.lean`, for every
`k ≥ 2`.

`g2lb_sound`: `g2lb k e ≤ 2 g(graphOf k e)`, where `g` is Dong-Cao's `dcG = q - D` (connected) or `0`
(disconnected).  Connectivity comes from the distance check `connB`, `2D` is exact, `q ≥ cc(G - S) - |S|` comes
from a labelling of `V \ S` that is constant along edges (only the check `respectsB` is used), and `g ≥ 0` always
(`dcG_nonneg`) covers graphs that fail the connectivity check.  `checkTab_sound` turns the table check into
`GTabSound`.  Nothing here needs `p(G) = q(G)`.
-/
import BHH.Interfaces
import BHHCert.GTab

open Finset

namespace BHH.E

open BHH.Cert

/-! ## lists over `Fin k` -/

lemma allBelow_iff (f : ℕ → Bool) : ∀ n, allBelow f n = true ↔ ∀ i < n, f i = true
  | 0 => by simp [allBelow]
  | n + 1 => by
    rw [allBelow]
    split_ifs with h
    · rw [allBelow_iff f n]
      constructor
      · intro H i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact H i hi
        · exact h
      · intro H i hi; exact H i (by omega)
    · simp only [false_iff, not_forall]
      exact ⟨n, by omega, h⟩

lemma countP_finRange (k : ℕ) (p : Fin k → Bool) :
    (List.finRange k).countP p = (univ.filter fun v => p v = true).card := by
  rw [Fin.univ_def, List.countP_eq_length_filter]
  rfl

lemma sum_finRange (k : ℕ) (f : Fin k → ℤ) : ((List.finRange k).map f).sum = ∑ v : Fin k, f v := by
  rw [Fin.univ_def]
  rfl

lemma foldl_max_le {α : Type*} (l : List α) (f : α → ℤ) (b q : ℤ) (hb : b ≤ q) (hf : ∀ a ∈ l, f a ≤ q) :
    l.foldl (fun acc a => max acc (f a)) b ≤ q := by
  induction l generalizing b with
  | nil => exact hb
  | cons a l ih => exact ih _ (max_le hb (hf a (by simp))) (fun a' ha' => hf a' (by simp [ha']))

/-! ## adjacency -/

lemma graphOf_adj_iff (k e : ℕ) (i j : Fin k) : (graphOf k e).Adj i j ↔ adjB k e i j = true := by
  simp only [graphOf, adjB, Bool.and_eq_true, bne_iff_ne, ne_eq, List.any_eq_true, List.mem_range,
    Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hij, p, hp, h1, h2⟩
    exact ⟨fun h => hij (Fin.ext h), p, hp, h1, h2⟩
  · rintro ⟨hij, p, hp, h1, h2⟩
    exact ⟨fun h => hij (congrArg Fin.val h), p, hp, h1, h2⟩

/-! ## connectivity -/

lemma connected_of_dist {k : ℕ} (hk : 0 < k) (G : SimpleGraph (Fin k)) (dist : Fin k → ℕ)
    (h : ∀ v : Fin k, v.val ≠ 0 → ∃ u, G.Adj u v ∧ dist u < dist v) : G.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨0, hk⟩, ?_⟩
  suffices H : ∀ n, ∀ v : Fin k, dist v ≤ n → G.Reachable ⟨0, hk⟩ v from fun v => H _ v le_rfl
  intro n
  induction n with
  | zero =>
    intro v hv
    by_cases h0 : v.val = 0
    · have hv0 : v = ⟨0, hk⟩ := Fin.ext h0
      rw [hv0]
    · obtain ⟨u, _, hu⟩ := h v h0
      omega
  | succ n ih =>
    intro v hv
    by_cases h0 : v.val = 0
    · have hv0 : v = ⟨0, hk⟩ := Fin.ext h0
      rw [hv0]
    · obtain ⟨u, hadj, hu⟩ := h v h0
      exact (ih u (by omega)).trans hadj.reachable

theorem connB_sound {k e : ℕ} (hk : 0 < k) (h : connB k e = true) : (graphOf k e).Connected := by
  simp only [connB, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
    Bool.and_eq_true, decide_eq_true_eq] at h
  apply connected_of_dist hk _ (fun v => (bfsDist k e).getD v.val 0)
  intro v hv
  rcases h v.val v.isLt with h0 | ⟨u, hu, hadj, hlt⟩
  · exact absurd h0 hv
  · exact ⟨⟨u, hu⟩, (graphOf_adj_iff k e _ _).mpr hadj, hlt⟩

/-! ## degrees and `D` -/

lemma degree_eq_natCard {V : Type*} (G : SimpleGraph V) (v : V) {inst : Fintype (G.neighborSet v)} :
    @SimpleGraph.degree V G v inst = Nat.card (G.neighborSet v) := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, Nat.card_eq_fintype_card]

lemma natCard_neighborSet_graphOf (k e : ℕ) (v : Fin k) :
    Nat.card ((graphOf k e).neighborSet v) = degB k e v := by
  classical
  rw [← degree_eq_natCard (inst := inferInstance), degB, countP_finRange]
  unfold SimpleGraph.degree
  congr 1
  ext u
  simp [SimpleGraph.mem_neighborFinset, graphOf_adj_iff]

lemma two_dcD (k e : ℕ) : 2 * dcD (graphOf k e) = (d2B k e : ℝ) := by
  unfold dcD d2B
  rw [sum_finRange]
  simp only [degree_eq_natCard, natCard_neighborSet_graphOf]
  push_cast
  ring

/-! ## `q ≥ cc(G - S) - |S|` from labellings -/

/-- vertices outside `S` with pairwise different values `g v = f v` lie in different components of `G - S` -/
theorem card_fixed_le_ccDel {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Finset V)
    (f g : V → ℕ) (hg : Function.Injective g) (hf : ∀ u v, u ∉ S → v ∉ S → G.Adj u v → f u = f v)
    (T : Finset V) (hT : ∀ v ∈ T, v ∉ S ∧ f v = g v) : T.card ≤ ccDel G S := by
  classical
  set H := G.induce ((S : Set V)ᶜ) with hH
  have key : ∀ (v w : ((S : Set V)ᶜ : Set V)) (p : H.Walk v w), f v.val = f w.val := by
    intro v w p
    induction p with
    | nil => rfl
    | @cons a b c h _ ih => exact (hf a.val b.val a.property b.property h).trans ih
  let F : H.ConnectedComponent → ℕ :=
    SimpleGraph.ConnectedComponent.lift (fun v => f v.val) (fun v w p _ => key v w p)
  unfold ccDel
  rw [← hH, Nat.card_eq_fintype_card]
  have hinj : Function.Injective fun v : T => H.connectedComponentMk ⟨v.1, (hT v.1 v.2).1⟩ := by
    intro a b hab
    have h1 := congrArg F hab
    simp only [F, SimpleGraph.ConnectedComponent.lift_mk] at h1
    apply Subtype.ext
    apply hg
    rw [← (hT a.1 a.2).2, ← (hT b.1 b.2).2]
    exact h1
  have := Fintype.card_le_of_injective _ hinj
  rwa [Fintype.card_coe] at this

lemma one_le_dcQ {V : Type*} [Fintype V] (G : SimpleGraph V) : 1 ≤ dcQ G :=
  le_trans (le_max_left _ _) (le_max_left _ _)

lemma cc_le_dcQ {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Finset V) :
    (ccDel G S : ℤ) - S.card ≤ dcQ G :=
  le_trans (Finset.le_sup' (fun S : Finset V => (ccDel G S : ℤ) - S.card) (mem_univ S)) (le_max_right _ _)

lemma ccLB_le (k e S : ℕ) : ccLB k e S ≤ dcQ (graphOf k e) := by
  unfold ccLB
  dsimp only
  split_ifs with h
  · set f := labels k e S
    set S' : Finset (Fin k) := univ.filter fun v => S.testBit v = true
    have hr : ∀ u v : Fin k, u ∉ S' → v ∉ S' → (graphOf k e).Adj u v → f.getD u 0 = f.getD v 0 := by
      intro u v hu hv hadj
      simp only [S', mem_filter, mem_univ, true_and, Bool.not_eq_true] at hu hv
      simp only [respectsB, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
        Bool.not_eq_true', beq_iff_eq] at h
      rcases h u v with ((h1 | h1) | h1) | h1
      · rw [hu] at h1; exact absurd h1 (by simp)
      · rw [hv] at h1; exact absurd h1 (by simp)
      · rw [(graphOf_adj_iff k e u v).mp hadj] at h1; exact absurd h1 (by simp)
      · exact h1
    have hT := card_fixed_le_ccDel (graphOf k e) S' (fun v => f.getD v 0) (fun v => v.val) Fin.val_injective hr
      (univ.filter fun v : Fin k => (!S.testBit v && f.getD v 0 == v.val) = true) (by
        intro v hv
        simp only [mem_filter, mem_univ, true_and, Bool.and_eq_true, Bool.not_eq_true',
          beq_iff_eq] at hv
        refine ⟨?_, hv.2⟩
        simp only [S', mem_filter, mem_univ, true_and, Bool.not_eq_true]
        exact hv.1)
    have h2 := cc_le_dcQ (graphOf k e) S'
    rw [countP_finRange, countP_finRange]
    have hS' : (univ.filter fun v : Fin k => S.testBit v = true).card = S'.card := rfl
    rw [hS']
    omega
  · exact one_le_dcQ _

lemma qLB_le (k e : ℕ) : qLB k e ≤ dcQ (graphOf k e) :=
  foldl_max_le _ _ _ _ (one_le_dcQ _) fun S _ => ccLB_le k e S

/-! ## `g ≥ 0` -/

theorem dcG_nonneg {V : Type*} [Fintype V] [Nontrivial V] (G : SimpleGraph V) : 0 ≤ dcG G := by
  classical
  unfold dcG
  split_ifs with hc
  · have hD : dcD G ≤ (n1 G : ℝ) / 2 := by
      unfold dcD n1
      simp only [degree_eq_natCard]
      rw [Finset.card_filter]
      push_cast
      rw [one_div, inv_mul_eq_div]
      gcongr with v hv
      have hpos := hc.preconnected.degree_pos_of_nontrivial v
      rw [degree_eq_natCard] at hpos
      split_ifs with h1
      · rw [h1]; norm_num
      · have h2 : 2 ≤ Nat.card (G.neighborSet v) := by omega
        have h3 : (2 : ℝ) ≤ Nat.card (G.neighborSet v) := by exact_mod_cast h2
        simp only [max_le_iff, le_refl, and_true]
        linarith
    have hq : (n1 G : ℝ) / 2 ≤ dcQ G := by
      have h1 : (n1 G : ℝ) / 2 ≤ ⌈(n1 G : ℝ) / 2⌉ := Int.le_ceil _
      have h2 : ⌈(n1 G : ℝ) / 2⌉ ≤ dcQ G := le_trans (le_max_right _ _) (le_max_left _ _)
      exact le_trans h1 (by exact_mod_cast h2)
    linarith
  · exact le_refl 0

/-! ## the per-graph bound -/

theorem g2lb_sound {k : ℕ} (hk : 2 ≤ k) (e : ℕ) : (g2lb k e : ℝ) ≤ 2 * dcG (graphOf k e) := by
  unfold g2lb
  split_ifs with hc
  · have hconn := connB_sound (by omega) hc
    unfold dcG
    rw [ite_eq_left hconn]
    have h1 : (qLB k e : ℝ) ≤ dcQ (graphOf k e) := by exact_mod_cast qLB_le k e
    have h2 := two_dcD k e
    push_cast
    linarith
  · have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
    have := dcG_nonneg (graphOf k e)
    push_cast
    linarith

/-! ## the table check -/

lemma digitsOK_iff (idx e : ℕ) : ∀ n, digitsOK idx e n = true ↔
    ∀ p < n, (idx / 3 ^ p % 3 = 1 → e.testBit p = true) ∧ (idx / 3 ^ p % 3 = 0 → e.testBit p = false)
  | 0 => by simp [digitsOK]
  | n + 1 => by
    rw [digitsOK]
    split_ifs with h
    · rw [digitsOK_iff idx e n]
      simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at h
      constructor
      · intro H p hp
        rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp | rfl
        · exact H p hp
        · exact ⟨fun h1 => h.1.resolve_left (not_not.mpr h1), fun h0 => h.2.resolve_left (not_not.mpr h0)⟩
      · intro H p hp; exact H p (by omega)
    · simp only [false_iff, not_forall]
      refine ⟨n, by omega, fun H => h ?_⟩
      have H1 := H.1
      have H2 := H.2
      simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true']
      constructor
      · by_cases h1 : idx / 3 ^ n % 3 = 1
        · exact Or.inr (H1 h1)
        · exact Or.inl h1
      · by_cases h0 : idx / 3 ^ n % 3 = 0
        · exact Or.inr (H2 h0)
        · exact Or.inl h0

lemma g2arr_getD {k e : ℕ} (he : e < 2 ^ (pairList k).length) : (g2arr k).getD e 0 = g2lb k e := by
  simp [g2arr, Array.getD_eq_getD_getElem?, he]

theorem checkTab_sound {k : ℕ} (hk : 2 ≤ k) (gt : GTab) (h : checkTab k gt.gmin = true) :
    GTabSound k gt := by
  intro idx e hidx hc
  simp only [checkTab, allBelow_iff, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  have he : e < 2 ^ (pairList k).length := hc.1
  rcases h idx hidx e he with h1 | h1
  · have hd : digitsOK idx e (pairList k).length = true := by
      rw [digitsOK_iff]
      intro p hp
      refine ⟨fun h1 => hc.2 p hp |>.1 h1, fun h0 => ?_⟩
      have := (hc.2 p hp).2 h0
      simpa using this
    rw [hd] at h1
    exact absurd h1 (by simp)
  · rw [g2arr_getD he] at h1
    calc (gt.gmin idx : ℝ) ≤ g2lb k e := by exact_mod_cast h1
      _ ≤ 2 * dcG (graphOf k e) := g2lb_sound hk e

end BHH.E

namespace BHH

-- the deliverables of this file, also under `BHH` (helpers stay in `BHH.E`)
export E (g2lb_sound checkTab_sound)

end BHH
