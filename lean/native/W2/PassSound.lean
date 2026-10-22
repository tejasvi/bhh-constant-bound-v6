/-
Soundness of the window-2 pass (paper Lemma 4.3, in the direction needed): for edge indicators `a1 i` (edge
`{i, i-1}`) and `a2 i` (edge `{i, i-2}`), the value returned by the pass of `W2Cert/Pass.lean` is at most
`2 Λ(H)` for the graph `H` on `Fin k` with exactly these edges.
-/
import W2.Graph
import W2Cert.Pass

open SimpleGraph W2C

namespace BHH.W2

variable (a1 a2 : ℕ → Bool)

/-- Adjacency on `ℕ`: the edges `{i, i-1}` with `a1 i` and `{i, i-2}` with `a2 i`. -/
def seqAdj (a b : ℕ) : Prop :=
  (b + 1 = a ∧ a1 a = true) ∨ (b + 2 = a ∧ a2 a = true) ∨
  (a + 1 = b ∧ a1 b = true) ∨ (a + 2 = b ∧ a2 b = true)

variable {a1 a2}

lemma seqAdj_symm {a b : ℕ} (h : seqAdj a1 a2 a b) : seqAdj a1 a2 b a := by
  unfold seqAdj at *; tauto

lemma seqAdj_irrefl (a : ℕ) : ¬ seqAdj a1 a2 a a := by
  unfold seqAdj; omega

lemma seqAdj_near {a b : ℕ} (h : seqAdj a1 a2 a b) : a ≤ b + 2 ∧ b ≤ a + 2 := by
  unfold seqAdj at h; omega

variable (a1 a2)

/-- The graph on `Fin k` of the edges given by `a1`, `a2`. -/
def seqGraph (k : ℕ) : SimpleGraph (Fin k) where
  Adj a b := seqAdj a1 a2 a.val b.val
  symm := ⟨fun _ _ h => seqAdj_symm h⟩
  loopless := ⟨fun a h => seqAdj_irrefl a.val h⟩

/-- The pass on the points `0, ..., i`. -/
def runPass : ℕ → Option St
  | 0 => some St.init
  | i + 1 => (runPass i).bind fun s => s.step (a1 (i + 1)) (a2 (i + 1))

/-- Twice the value returned by the pass on `k` points. -/
def passVal2 (k : ℕ) : ℕ :=
  match runPass a1 a2 (k - 1) with
  | none => 0
  | some s => s.close2

/-- Adjacency within the prefix `{0, ..., i}`. -/
def pAdj (i : ℕ) (x y : ℕ) : Prop := seqAdj a1 a2 x y ∧ x ≤ i ∧ y ≤ i

/-- Reachability within the prefix `{0, ..., i}`. -/
def P (i : ℕ) : ℕ → ℕ → Prop := Relation.ReflTransGen (pAdj a1 a2 i)

/-- The degree of `v` in the prefix `{0, ..., i}`. -/
def degP (i v : ℕ) : ℕ :=
  (if 1 ≤ v ∧ a1 v = true then 1 else 0) + (if 2 ≤ v ∧ a2 v = true then 1 else 0) +
  (if v + 1 ≤ i ∧ a1 (v + 1) = true then 1 else 0) + (if v + 2 ≤ i ∧ a2 (v + 2) = true then 1 else 0)

variable {a1 a2}

lemma P_mono {i j a b : ℕ} (hij : i ≤ j) (h : P a1 a2 i a b) : P a1 a2 j a b := by
  have hle : pAdj a1 a2 i ≤ pAdj a1 a2 j :=
    fun x y hxy => ⟨hxy.1, le_trans hxy.2.1 hij, le_trans hxy.2.2 hij⟩
  exact Relation.ReflTransGen.mono hle a b h

lemma P_symm {i a b : ℕ} (h : P a1 a2 i a b) : P a1 a2 i b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head ⟨seqAdj_symm hbc.1, hbc.2.2, hbc.2.1⟩ ih

lemma P_trans {i a b c : ℕ} (h1 : P a1 a2 i a b) (h2 : P a1 a2 i b c) : P a1 a2 i a c :=
  Relation.ReflTransGen.trans h1 h2

lemma P_edge {i a b : ℕ} (h : seqAdj a1 a2 a b) (ha : a ≤ i) (hb : b ≤ i) : P a1 a2 i a b :=
  Relation.ReflTransGen.single ⟨h, ha, hb⟩

/-- The invariant of the pass after the points `0, ..., i` (`i ≥ 1`), soundness direction. -/
structure Inv (i : ℕ) (s : St) : Prop where
  two : s.two = true
  d0 : s.d0 = cap2 (degP a1 a2 i i)
  d1 : s.d1 = cap2 (degP a1 a2 i (i - 1))
  same : s.same = true → P a1 a2 i i (i - 1)
  cover : ∀ v ≤ i, P a1 a2 i v i ∨ P a1 a2 i v (i - 1)
  u : ((Finset.range (i - 1)).filter fun v => degP a1 a2 i v < 2).card ≤ s.u

lemma cap2_cap2_add (x y : ℕ) : cap2 (cap2 x + y) = cap2 (x + y) := by
  unfold cap2; omega

lemma inv_one {s : St} (h : runPass a1 a2 1 = some s) : Inv (a1 := a1) (a2 := a2) 1 s := by
  simp only [runPass, Option.bind, St.step, St.init] at h
  simp only [Bool.not_false, ite_true, Option.some.injEq] at h
  subst h
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [degP, cap2, b2n]; split_ifs <;> simp_all
  · simp only [degP, cap2, b2n]; split_ifs <;> simp_all
  · intro hs
    simp only at hs
    exact P_edge (Or.inl ⟨rfl, hs⟩) le_rfl (by omega)
  · intro v hv
    rcases Nat.lt_or_ge v 1 with h | h
    · right; have : v = 0 := by omega
      subst this; exact Relation.ReflTransGen.refl
    · left; have : v = 1 := by omega
      subst this; exact Relation.ReflTransGen.refl
  · simp

lemma degP_succ_self {i : ℕ} (hi : 1 ≤ i) :
    degP a1 a2 (i + 1) (i + 1) = b2n (a1 (i + 1)) + b2n (a2 (i + 1)) := by
  unfold degP b2n
  have h1 : 1 ≤ i + 1 := by omega
  have h2 : 2 ≤ i + 1 := by omega
  have h3 : ¬ (i + 1 + 1 ≤ i + 1) := by omega
  have h4 : ¬ (i + 1 + 2 ≤ i + 1) := by omega
  simp only [h1, h2, h3, h4, true_and, false_and, ite_false, add_zero]
  all_goals (cases a1 (i + 1) <;> cases a2 (i + 1) <;> simp)

lemma degP_succ_prev (i : ℕ) :
    degP a1 a2 (i + 1) i = degP a1 a2 i i + b2n (a1 (i + 1)) := by
  unfold degP b2n
  have h3 : i + 1 ≤ i + 1 := le_rfl
  have h3' : ¬ (i + 1 ≤ i) := by omega
  have h4 : ¬ (i + 2 ≤ i + 1) := by omega
  have h4' : ¬ (i + 2 ≤ i) := by omega
  simp only [h3, h3', h4, h4', true_and, false_and, ite_false, add_zero]
  all_goals (cases a1 (i + 1) <;> simp)

lemma degP_succ_prev2 {i : ℕ} (hi : 1 ≤ i) :
    degP a1 a2 (i + 1) (i - 1) = degP a1 a2 i (i - 1) + b2n (a2 (i + 1)) := by
  unfold degP b2n
  have e1 : i - 1 + 1 = i := by omega
  have e2 : i - 1 + 2 = i + 1 := by omega
  rw [e1, e2]
  have h3 : i ≤ i + 1 := by omega
  have h3' : i ≤ i := le_rfl
  have h4 : i + 1 ≤ i + 1 := le_rfl
  have h4' : ¬ (i + 1 ≤ i) := by omega
  simp only [h3, h3', h4, h4', true_and, false_and, ite_false, add_zero]
  all_goals (cases a2 (i + 1) <;> simp)

lemma degP_succ_low {i v : ℕ} (hv : v + 2 ≤ i) : degP a1 a2 (i + 1) v = degP a1 a2 i v := by
  unfold degP
  have h3 : v + 1 ≤ i + 1 := by omega
  have h3' : v + 1 ≤ i := by omega
  have h4 : v + 2 ≤ i + 1 := by omega
  simp only [h3, h3', h4, hv, true_and]

lemma cap2_le_two (x : ℕ) : cap2 x ≤ 2 := by unfold cap2; omega

lemma cap2_lt_two_iff (x : ℕ) : cap2 x < 2 ↔ x < 2 := by unfold cap2; omega

lemma b2n_le_one (b : Bool) : b2n b ≤ 1 := by cases b <;> simp [b2n]

/-- The successful step from a two-point window. -/
lemma step_two_some {s s' : St} {a b : Bool} (h2 : s.two = true) (h : s.step a b = some s') :
    s' = ⟨true, a || (b && s.same), b2n a + b2n b, cap2 (s.d0 + b2n a),
      s.u + (if cap2 (s.d1 + b2n b) < 2 then 1 else 0)⟩ ∧ (b = true ∨ s.same = true) := by
  unfold St.step at h
  rw [h2] at h
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h
  by_cases hu : 2 ≤ s.u + (if cap2 (s.d1 + b2n b) < 2 then 1 else 0)
  · simp only [hu, ite_true, reduceCtorEq] at h
  · simp only [hu, ite_false] at h
    by_cases hc : (!(b || s.same)) = true
    · simp only [hc, ite_true, reduceCtorEq] at h
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      refine ⟨h.symm, ?_⟩
      cases b <;> cases hs : s.same <;> simp_all

/-- One step of the pass preserves the invariant. -/
lemma inv_step {i : ℕ} (hi : 1 ≤ i) {s s' : St} (hs : Inv (a1 := a1) (a2 := a2) i s)
    (hstep : s.step (a1 (i + 1)) (a2 (i + 1)) = some s') : Inv (a1 := a1) (a2 := a2) (i + 1) s' := by
  obtain ⟨rfl, hcon'⟩ := step_two_some hs.two hstep
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · -- d0
    show b2n (a1 (i + 1)) + b2n (a2 (i + 1)) = cap2 (degP a1 a2 (i + 1) (i + 1))
    rw [degP_succ_self hi]
    have := b2n_le_one (a1 (i + 1)); have := b2n_le_one (a2 (i + 1))
    unfold cap2; omega
  · -- d1
    show cap2 (s.d0 + b2n (a1 (i + 1))) = cap2 (degP a1 a2 (i + 1) (i + 1 - 1))
    rw [show i + 1 - 1 = i by omega, degP_succ_prev, hs.d0, cap2_cap2_add]
  · -- same
    intro hsame
    show P a1 a2 (i + 1) (i + 1) (i + 1 - 1)
    rw [show i + 1 - 1 = i by omega]
    simp only [Bool.or_eq_true, Bool.and_eq_true] at hsame
    rcases hsame with h1 | ⟨h2, h3⟩
    · exact P_edge (Or.inl ⟨rfl, h1⟩) le_rfl (by omega)
    · have e : seqAdj a1 a2 (i + 1) (i - 1) := Or.inr (Or.inl ⟨by omega, h2⟩)
      exact P_trans (P_edge e le_rfl (by omega)) (P_symm (P_mono (by omega) (hs.same h3)))
  · -- cover
    intro v hv
    show P a1 a2 (i + 1) v (i + 1) ∨ P a1 a2 (i + 1) v (i + 1 - 1)
    rw [show i + 1 - 1 = i by omega]
    rcases Nat.lt_or_ge i v with hvi | hvi
    · left; have : v = i + 1 := by omega
      subst this; exact Relation.ReflTransGen.refl
    · rcases hs.cover v hvi with h | h
      · right; exact P_mono (by omega) h
      · rcases hcon' with h2 | h3
        · left
          have e : seqAdj a1 a2 (i - 1) (i + 1) := Or.inr (Or.inr (Or.inr ⟨by omega, h2⟩))
          exact P_trans (P_mono (by omega) h) (P_edge e (by omega) le_rfl)
        · right
          exact P_mono (by omega) (P_trans h (P_symm (hs.same h3)))
  · -- u
    show ((Finset.range (i + 1 - 1)).filter fun v => degP a1 a2 (i + 1) v < 2).card ≤
      s.u + (if cap2 (s.d1 + b2n (a2 (i + 1))) < 2 then 1 else 0)
    rw [show i + 1 - 1 = i by omega]
    have hsplit : Finset.range i = insert (i - 1) (Finset.range (i - 1)) := by
      rw [show i = (i - 1) + 1 by omega, Finset.range_add_one]; simp
    rw [hsplit, Finset.filter_insert]
    have hlow : ((Finset.range (i - 1)).filter fun v => degP a1 a2 (i + 1) v < 2) =
        ((Finset.range (i - 1)).filter fun v => degP a1 a2 i v < 2) := by
      apply Finset.filter_congr
      intro v hv
      rw [Finset.mem_range] at hv
      rw [degP_succ_low (by omega)]
    have hd : cap2 (s.d1 + b2n (a2 (i + 1))) < 2 ↔ degP a1 a2 (i + 1) (i - 1) < 2 := by
      rw [hs.d1, cap2_cap2_add, degP_succ_prev2 hi, cap2_lt_two_iff]
    have hu0 := hs.u
    split_ifs with h1 h2 h2
    · rw [Finset.card_insert_of_notMem (by simp), hlow]; omega
    · exact absurd (hd.mpr h1) h2
    · rw [hlow]; omega
    · rw [hlow]; omega

/-- The invariant holds after every successful prefix. -/
lemma inv_all : ∀ i, 1 ≤ i → ∀ s, runPass a1 a2 i = some s → Inv (a1 := a1) (a2 := a2) i s
  | 0, h, _, _ => absurd h (by omega)
  | 1, _, s, h => inv_one h
  | i + 2, _, s', h => by
    have h' : (runPass a1 a2 (i + 1)).bind (fun s => s.step (a1 (i + 1 + 1)) (a2 (i + 1 + 1))) = some s' := h
    cases hp : runPass a1 a2 (i + 1) with
    | none => rw [hp] at h'; simp at h'
    | some s =>
      rw [hp] at h'
      simp only [Option.bind_some] at h'
      exact inv_step (by omega) (inv_all (i + 1) (by omega) s hp) h'

/-! ## Bridges to `SimpleGraph` -/

lemma sum_ind_eq (k c : ℕ) (p : Prop) [Decidable p] :
    (∑ w ∈ Finset.range k, (if w = c ∧ p then 1 else 0 : ℕ)) = if c < k ∧ p then 1 else 0 := by
  by_cases hp : p
  · simp only [hp, and_true]
    rw [Finset.sum_ite_eq' (Finset.range k) c (fun _ => (1 : ℕ))]
    simp [Finset.mem_range]
  · simp [hp]

open Classical in
/-- The degree in `seqGraph` is `degP` for the full prefix. -/
lemma degree_seqGraph (k v : ℕ) (hv : v < k) :
    (seqGraph a1 a2 k).degree ⟨v, hv⟩ = degP a1 a2 (k - 1) v := by
  classical
  rw [← card_neighborFinset_eq_degree]
  have e1 : (seqGraph a1 a2 k).neighborFinset ⟨v, hv⟩ =
      Finset.univ.filter (fun w : Fin k => seqAdj a1 a2 v w.val) := by
    ext w; simp only [mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and]; rfl
  rw [e1]
  have e2 : (Finset.univ.filter (fun w : Fin k => seqAdj a1 a2 v w.val)).card =
      ((Finset.range k).filter (fun w => seqAdj a1 a2 v w)).card := by
    rw [← Finset.card_map ⟨Fin.val, Fin.val_injective⟩]
    congr 1
    ext w
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk,
      Finset.mem_range]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x.isLt, hx⟩
    · rintro ⟨hw, hx⟩; exact ⟨⟨w, hw⟩, hx, rfl⟩
  rw [e2, Finset.card_filter]
  have e3 : ∀ w, (if seqAdj a1 a2 v w then 1 else 0 : ℕ) =
      (if w = v - 1 ∧ (1 ≤ v ∧ a1 v = true) then 1 else 0) + (if w = v - 2 ∧ (2 ≤ v ∧ a2 v = true) then 1 else 0) +
      (if w = v + 1 ∧ a1 (v + 1) = true then 1 else 0) + (if w = v + 2 ∧ a2 (v + 2) = true then 1 else 0) := by
    intro w
    unfold seqAdj
    by_cases h1 : w + 1 = v ∧ a1 v = true
    · have : w = v - 1 := by omega
      subst this
      simp only [h1, true_or, ite_true]
      have : ¬ (v - 1 = v - 2 ∧ 2 ≤ v ∧ a2 v = true) := by omega
      have h3 : ¬ (v - 1 = v + 1) := by omega
      have h4 : ¬ (v - 1 = v + 2) := by omega
      simp [this, h3, h4, h1.2, show 1 ≤ v by omega]
    · by_cases h2 : w + 2 = v ∧ a2 v = true
      · have : w = v - 2 := by omega
        subst this
        have h3 : ¬ (v - 2 = v - 1 ∧ 1 ≤ v ∧ a1 v = true) := by omega
        have h4 : ¬ (v - 2 = v + 1) := by omega
        have h5 : ¬ (v - 2 = v + 2) := by omega
        simp [h2, h3, h4, h5, show 2 ≤ v by omega]
      · by_cases h3 : v + 1 = w ∧ a1 w = true
        · obtain ⟨rfl, h3b⟩ := h3
          have h4 : ¬ (v + 1 = v - 1 ∧ 1 ≤ v ∧ a1 v = true) := by omega
          have h5 : ¬ (v + 1 = v - 2 ∧ 2 ≤ v ∧ a2 v = true) := by omega
          have h6 : ¬ (v + 1 = v + 2) := by omega
          simp [h3b, h4, h5, h6]
        · by_cases h4 : v + 2 = w ∧ a2 w = true
          · obtain ⟨rfl, h4b⟩ := h4
            have h5 : ¬ (v + 2 = v - 1 ∧ 1 ≤ v ∧ a1 v = true) := by omega
            have h6 : ¬ (v + 2 = v - 2 ∧ 2 ≤ v ∧ a2 v = true) := by omega
            have h7 : ¬ (v + 2 = v + 1) := by omega
            simp [h4b, h5, h6, h7]
          · have n1 : ¬ (w = v - 1 ∧ 1 ≤ v ∧ a1 v = true) := by
              rintro ⟨rfl, hv1, ha⟩; exact h1 ⟨by omega, ha⟩
            have n2 : ¬ (w = v - 2 ∧ 2 ≤ v ∧ a2 v = true) := by
              rintro ⟨rfl, hv2, ha⟩; exact h2 ⟨by omega, ha⟩
            have n3 : ¬ (w = v + 1 ∧ a1 (v + 1) = true) := by
              rintro ⟨rfl, ha⟩; exact h3 ⟨rfl, ha⟩
            have n4 : ¬ (w = v + 2 ∧ a2 (v + 2) = true) := by
              rintro ⟨rfl, ha⟩; exact h4 ⟨rfl, ha⟩
            have : ¬ ((w + 1 = v ∧ a1 v = true) ∨ (w + 2 = v ∧ a2 v = true) ∨
                (v + 1 = w ∧ a1 w = true) ∨ (v + 2 = w ∧ a2 w = true)) := by tauto
            simp only [this, n1, n2, n3, n4, ite_false]
  simp only [e3, Finset.sum_add_distrib, sum_ind_eq]
  unfold degP
  have c1 : (v - 1 < k ∧ 1 ≤ v ∧ a1 v = true) ↔ (1 ≤ v ∧ a1 v = true) :=
    ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
  have c2 : (v - 2 < k ∧ 2 ≤ v ∧ a2 v = true) ↔ (2 ≤ v ∧ a2 v = true) :=
    ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
  have c3 : (v + 1 < k ∧ a1 (v + 1) = true) ↔ (v + 1 ≤ k - 1 ∧ a1 (v + 1) = true) :=
    ⟨fun h => ⟨by omega, h.2⟩, fun h => ⟨by omega, h.2⟩⟩
  have c4 : (v + 2 < k ∧ a2 (v + 2) = true) ↔ (v + 2 ≤ k - 1 ∧ a2 (v + 2) = true) :=
    ⟨fun h => ⟨by omega, h.2⟩, fun h => ⟨by omega, h.2⟩⟩
  simp only [c1, c2, c3, c4]

/-- Reachability in the full prefix gives reachability in `seqGraph`. -/
lemma reachable_of_P {k a b : ℕ} (ha : a < k) (hb : b < k) (h : P a1 a2 (k - 1) a b) :
    (seqGraph a1 a2 k).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction h with
  | refl => exact Reachable.refl _
  | @tail c d _ hcd ih =>
    have hc : c < k := by have := hcd.2.1; omega
    have hd : d < k := by have := hcd.2.2; omega
    exact (ih hc).trans (Adj.reachable (G := seqGraph a1 a2 k) (u := ⟨c, hc⟩) (v := ⟨d, hd⟩) hcd.1)

/-! ## The bound -/

/-- The closing value as a function of the count `n` of vertices of degree `< 2`. -/
def cval (n : ℕ) : ℕ := if n == 0 then 2 else if n == 1 then 1 else 0

lemma cval_le {n m : ℕ} (h : m ≤ n) : (cval n : ℝ) ≤ max 0 (2 - (m : ℝ)) := by
  unfold cval
  by_cases h0 : n = 0
  · subst h0
    have : m = 0 := by omega
    subst this; norm_num
  · by_cases h1 : n = 1
    · subst h1
      have hm : (m : ℝ) ≤ 1 := by exact_mod_cast h
      simp only [Nat.reduceBEq, Bool.false_eq_true, ite_false, ite_true, Nat.cast_one]
      exact le_max_of_le_right (by linarith)
    · have e0 : (n == 0) = false := by simp [h0]
      have e1 : (n == 1) = false := by simp [h1]
      simp only [e0, e1, Bool.false_eq_true, ite_false, Nat.cast_zero]
      exact le_max_left _ _

lemma close2_eq (s : St) :
    s.close2 = if s.same = true then
      cval (s.u + (if s.d0 < 2 then 1 else 0) + (if s.d1 < 2 then 1 else 0)) else 0 := by
  unfold St.close2 cval; rfl

/-- `nLt2` of `seqGraph` as a count over `range k` with `degP`. -/
lemma nLt2_seqGraph (k : ℕ) :
    nLt2 (seqGraph a1 a2 k) = ((Finset.range k).filter fun v => degP a1 a2 (k - 1) v < 2).card := by
  classical
  unfold nLt2
  rw [← Finset.card_map ⟨Fin.val, Fin.val_injective⟩]
  congr 1
  ext w
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk,
    Finset.mem_range]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.isLt, ?_⟩
    have := degree_seqGraph (a1 := a1) (a2 := a2) k x.val x.isLt
    rw [← this]; convert hx
  · rintro ⟨hw, hx⟩
    refine ⟨⟨w, hw⟩, ?_, rfl⟩
    have := degree_seqGraph (a1 := a1) (a2 := a2) k w hw
    rw [← this] at hx; convert hx

/-- Lemma 4.3 (the direction used): the pass returns at most `2 Λ` of the graph of its input edges. -/
theorem passVal2_le_Lam {k : ℕ} (hk : 2 ≤ k) :
    (passVal2 a1 a2 k : ℝ) ≤ 2 * Lam (seqGraph a1 a2 k) := by
  classical
  have hL := Lam_nonneg (seqGraph a1 a2 k)
  unfold passVal2
  cases h : runPass a1 a2 (k - 1) with
  | none => simp only [Nat.cast_zero]; linarith
  | some s =>
    simp only
    have hinv := inv_all (k - 1) (by omega) s h
    rw [close2_eq]
    by_cases hsame : s.same = true
    · rw [if_pos hsame]
      have hreach : ∀ v, v < k → P a1 a2 (k - 1) v (k - 1) := by
        intro v hv
        rcases hinv.cover v (by omega) with h1 | h1
        · exact h1
        · exact P_trans h1 (P_symm (hinv.same hsame))
      have hconn : (seqGraph a1 a2 k).Connected := by
        have hne : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
        refine ⟨fun u v => ?_⟩
        have hu := reachable_of_P u.isLt (by omega : k - 1 < k) (hreach u.val u.isLt)
        have hv := reachable_of_P v.isLt (by omega : k - 1 < k) (hreach v.val v.isLt)
        exact hu.trans hv.symm
      have hn : nLt2 (seqGraph a1 a2 k) ≤
          s.u + (if s.d0 < 2 then 1 else 0) + (if s.d1 < 2 then 1 else 0) := by
        rw [nLt2_seqGraph]
        have hsplit : Finset.range k = insert (k - 1) (insert (k - 2) (Finset.range (k - 2))) := by
          rw [show k = (k - 2) + 1 + 1 by omega, Finset.range_add_one, Finset.range_add_one]
          simp
        rw [hsplit, Finset.filter_insert, Finset.filter_insert]
        have hu := hinv.u
        rw [show k - 1 - 1 = k - 2 by omega] at hu
        have hd0 : s.d0 < 2 ↔ degP a1 a2 (k - 1) (k - 1) < 2 := by rw [hinv.d0, cap2_lt_two_iff]
        have hd1 : s.d1 < 2 ↔ degP a1 a2 (k - 1) (k - 2) < 2 := by
          rw [hinv.d1, cap2_lt_two_iff, show k - 1 - 1 = k - 2 by omega]
        have c1 := Finset.card_insert_le (k - 1)
          (if degP a1 a2 (k - 1) (k - 2) < 2 then insert (k - 2)
            ((Finset.range (k - 2)).filter fun v => degP a1 a2 (k - 1) v < 2)
          else (Finset.range (k - 2)).filter fun v => degP a1 a2 (k - 1) v < 2)
        have c2 := Finset.card_insert_le (k - 2)
          ((Finset.range (k - 2)).filter fun v => degP a1 a2 (k - 1) v < 2)
        split_ifs at * with e1 e2 e2 <;> simp_all <;> omega
      have hc := cval_le hn
      unfold Lam
      simp only [hconn, ite_true]
      have : 2 * max 0 (1 - (nLt2 (seqGraph a1 a2 k) : ℝ) / 2) = max 0 (2 - (nLt2 (seqGraph a1 a2 k) : ℝ)) := by
        rw [mul_max_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]; ring_nf
      rw [this]; exact hc
    · rw [if_neg hsame]; simp only [Nat.cast_zero]; linarith

end BHH.W2
