/-
Soundness of the exact bisection tree `BHHCert/Tree.lean` (module E, item 1).

For EVERY decision function `dec` and every leaf function `L` with `LeafSoundProp k L`:
* `bnbExact_sound`: the value of the recursion on a box is at most `2^OS ∫_{box ∩ D_k} F2`;
* `initBox_subset`, `initBox_disjoint`: the initial boxes lie in `X_k` and are pairwise disjoint;
* `shardSum_add`, `shardSum_sound`: shard sums add up, and a shard sum is at most `2^OS ∫_{D_k ∩ X_k} F2`.
Only inclusion and disjointness are used (the direction `≥` of the bound), never a partition.
-/
import BHH.Interfaces
import BHHCert.Tree

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BHH.E

open BHH.Cert

/-! ## fixed point and measurability -/

lemma ONE_real : ((ONE : ℤ) : ℝ) = (2 : ℝ) ^ PR := by
  norm_num [ONE, PR]

lemma two_pow_PR_pos : (0 : ℝ) < (2 : ℝ) ^ PR := by positivity

lemma fx_mono {a b : ℤ} (h : a ≤ b) : fx a ≤ fx b := by
  unfold fx
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) two_pow_PR_pos.le

lemma fx_lt_iff {a b : ℤ} : fx a < fx b ↔ a < b := by
  unfold fx
  rw [div_lt_div_iff_of_pos_right two_pow_PR_pos]
  exact Int.cast_lt

lemma fx_mul_ONE (n : ℤ) : fx (n * ONE) = n := by
  unfold fx
  rw [Int.cast_mul, ONE_real]
  field_simp

lemma measurableSet_boxOf {m : ℕ} (lo hi : List ℤ) : MeasurableSet (boxOf lo hi : Set (Fin m → ℝ)) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

lemma measurable_xget {m : ℕ} (d : ℕ) : Measurable fun x : Fin m → ℝ => xget x d := by
  unfold xget
  by_cases h : d < m
  · simp only [h, dite_true]; exact measurable_pi_apply _
  · simp only [h, dite_false]; exact measurable_const

lemma measurableSet_Dk (k : ℕ) : MeasurableSet (Dk k) := by
  have e : Dk k = ({x | 0 ≤ xget x 0} ∩ {x | 0 ≤ xget x 2}) ∩
      ⋂ j : ℕ, {x | 2 ≤ j → j + 1 < k → xget x (2 * j - 3) ≤ xget x (2 * (j + 1) - 3)} := by
    ext x
    simp only [Dk, mem_ofPred_eq, mem_inter_iff, mem_iInter, and_assoc]
  rw [e]
  refine ((measurableSet_le measurable_const (measurable_xget 0)).inter
    (measurableSet_le measurable_const (measurable_xget 2))).inter (MeasurableSet.iInter fun j => ?_)
  by_cases h : 2 ≤ j ∧ j + 1 < k
  · have e2 : {x : Fin (mDim k) → ℝ | 2 ≤ j → j + 1 < k → xget x (2 * j - 3) ≤ xget x (2 * (j + 1) - 3)} =
        {x | xget x (2 * j - 3) ≤ xget x (2 * (j + 1) - 3)} := by
      ext x; simp only [mem_ofPred_eq, h.1, h.2, true_implies]
    rw [e2]
    exact measurableSet_le (measurable_xget _) (measurable_xget _)
  · have e2 : {x : Fin (mDim k) → ℝ | 2 ≤ j → j + 1 < k → xget x (2 * j - 3) ≤ xget x (2 * (j + 1) - 3)} =
        univ := by
      ext x; simp only [mem_ofPred_eq, mem_univ, iff_true]
      intro h1 h2; exact absurd ⟨h1, h2⟩ h
    rw [e2]
    exact MeasurableSet.univ

/-! ## lists -/

lemma getD_set_eq (l : List ℤ) (d : ℕ) (v : ℤ) (d' : ℕ) :
    (l.set d v).getD d' 0 = if d = d' ∧ d < l.length then v else l.getD d' 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set, List.getD_eq_getElem?_getD]
  by_cases h1 : d = d'
  · subst h1
    by_cases h2 : d < l.length
    · simp [h2]
    · simp only [h2, ite_false, and_false, ite_true]
      rw [List.getElem?_eq_none (by omega)]
  · simp [h1]

/-! ## halves of a box -/

lemma boxOf_lower_subset {m : ℕ} (lo hi : List ℤ) (d : ℕ) :
    (boxOf lo (hi.set d ((lo.getD d 0 + hi.getD d 0) / 2)) : Set (Fin m → ℝ)) ⊆ boxOf lo hi := by
  intro x hx
  simp only [boxOf, mem_pi, mem_univ, true_implies, mem_Ico] at hx ⊢
  intro i
  obtain ⟨h1, h2⟩ := hx i
  rw [getD_set_eq] at h2
  refine ⟨h1, ?_⟩
  split_ifs at h2 with hdi
  · obtain ⟨rfl, _⟩ := hdi
    have a1 : lo.getD i 0 < (lo.getD i 0 + hi.getD i 0) / 2 := fx_lt_iff.mp (lt_of_le_of_lt h1 h2)
    have a2 : (lo.getD i 0 + hi.getD i 0) / 2 ≤ hi.getD i 0 := by omega
    exact lt_of_lt_of_le h2 (fx_mono a2)
  · exact h2

lemma boxOf_upper_subset {m : ℕ} (lo hi : List ℤ) (d : ℕ) :
    (boxOf (lo.set d ((lo.getD d 0 + hi.getD d 0) / 2)) hi : Set (Fin m → ℝ)) ⊆ boxOf lo hi := by
  intro x hx
  simp only [boxOf, mem_pi, mem_univ, true_implies, mem_Ico] at hx ⊢
  intro i
  obtain ⟨h1, h2⟩ := hx i
  rw [getD_set_eq] at h1
  refine ⟨?_, h2⟩
  split_ifs at h1 with hdi
  · obtain ⟨rfl, _⟩ := hdi
    have a1 : (lo.getD i 0 + hi.getD i 0) / 2 < hi.getD i 0 := fx_lt_iff.mp (lt_of_le_of_lt h1 h2)
    have a2 : lo.getD i 0 ≤ (lo.getD i 0 + hi.getD i 0) / 2 := by omega
    exact le_trans (fx_mono a2) h1
  · exact h1

lemma boxOf_halves_disjoint {m : ℕ} (lo hi : List ℤ) (d : ℕ) (mid : ℤ) (hdm : d < m)
    (hlo : d < lo.length) (hhi : d < hi.length) :
    Disjoint (boxOf lo (hi.set d mid) : Set (Fin m → ℝ)) (boxOf (lo.set d mid) hi) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  simp only [boxOf, mem_pi, mem_univ, true_implies, mem_Ico] at hx1 hx2
  have a := (hx1 ⟨d, hdm⟩).2
  have b := (hx2 ⟨d, hdm⟩).1
  rw [getD_set_eq] at a b
  simp only [hlo, hhi, and_self, ite_true] at a b
  linarith

/-! ## the bisection recursion -/

lemma bnbExact_nonneg (k : ℕ) (dec : List ℤ → List ℤ → Dec) (L : List ℤ → List ℤ → ℤ) :
    ∀ fuel lo hi, 0 ≤ bnbExact k dec L fuel lo hi := by
  intro fuel
  induction fuel with
  | zero => intro lo hi; simp [bnbExact]
  | succ n ih =>
    intro lo hi
    simp only [bnbExact]
    split
    · split_ifs
      · exact add_nonneg (ih _ _) (ih _ _)
      · exact le_refl 0
    · split_ifs
      · exact le_max_right _ _
      · exact le_refl 0
    · exact le_refl 0

/-- the root box corners -/
lemma rootLo_length (k : ℕ) : (rootLo k).length = mDim k := by simp [rootLo, mDim]

lemma rootHi_length (k : ℕ) : (rootHi k).length = mDim k := by simp [rootHi, mDim]

lemma rootLo_getD (k d : ℕ) (hd : d < mDim k) :
    (rootLo k).getD d 0 = if d = 0 ∨ d = 2 then 0 else -((k : ℤ) - 2) * ONE := by
  unfold mDim at hd
  simp [rootLo, List.getD_eq_getElem?_getD, List.getElem?_range hd]

lemma rootHi_getD (k d : ℕ) (hd : d < mDim k) : (rootHi k).getD d 0 = ((k : ℤ) - 2) * ONE := by
  unfold mDim at hd
  simp [rootHi, List.getD_eq_getElem?_getD, hd]

lemma fx_rootLo (k d : ℕ) (hd : d < mDim k) :
    fx ((rootLo k).getD d 0) = if d = 0 ∨ d = 2 then 0 else -((k : ℝ) - 2) := by
  rw [rootLo_getD k d hd]
  split_ifs
  · simp [fx]
  · rw [fx_mul_ONE]; push_cast; ring

lemma fx_rootHi (k d : ℕ) (hd : d < mDim k) : fx ((rootHi k).getD d 0) = (k : ℝ) - 2 := by
  rw [rootHi_getD k d hd, fx_mul_ONE]; push_cast; ring

/-- the root box is `X_k` -/
lemma boxOf_root (k : ℕ) : (boxOf (rootLo k) (rootHi k) : Set (Fin (mDim k) → ℝ)) = Xk k := by
  ext x
  simp only [boxOf, Xk, mem_pi, mem_univ, true_implies, mem_Ico]
  refine forall_congr' fun i => ?_
  rw [fx_rootLo k i.val i.isLt, fx_rootHi k i.val i.isLt]

/-- the Bool test `validB` implies `ValidBox` -/
theorem validB_valid {k : ℕ} {lo hi : List ℤ} (h : validB k lo hi = true) : ValidBox k lo hi := by
  simp only [validB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨hlo, hhi⟩, hall⟩ := h
  have hall' : ∀ d < mDim k, lo.getD d 0 < hi.getD d 0 ∧ (lo.getD d 0 + hi.getD d 0) % 2 = 0 ∧
      (rootLo k).getD d 0 ≤ lo.getD d 0 ∧ hi.getD d 0 ≤ (rootHi k).getD d 0 := by
    intro d hd
    have := hall d hd
    simpa [and_assoc] using this
  refine ⟨hlo, hhi, fun d hd => ⟨(hall' d hd).1, Int.even_iff.mpr (hall' d hd).2.1⟩, ?_⟩
  rw [← boxOf_root k]
  intro x hx
  simp only [boxOf, mem_pi, mem_univ, true_implies, mem_Ico] at hx ⊢
  intro i
  obtain ⟨_, _, h3, h4⟩ := hall' i.val i.isLt
  exact ⟨le_trans (fx_mono h3) (hx i).1, lt_of_lt_of_le (hx i).2 (fx_mono h4)⟩

lemma bnbExact_length (k : ℕ) (dec : List ℤ → List ℤ → Dec) (L : List ℤ → List ℤ → ℤ) :
    ∀ fuel lo hi, lo.length ≠ mDim k → bnbExact k dec L fuel lo hi = 0 := by
  intro fuel
  induction fuel with
  | zero => intro lo hi _; simp [bnbExact]
  | succ n ih =>
    intro lo hi hl
    simp only [bnbExact]
    split
    · split_ifs
      · rw [ih _ _ hl, ih _ _ (by simpa using hl)]; rfl
      · rfl
    · split_ifs with hv
      · exact absurd (validB_valid hv).1 hl
      · rfl
    · rfl

lemma ofReal_max_div_le {a : ℤ} {c : ℝ} {I : ℝ≥0∞} (_hc : 0 < c) (h : ENNReal.ofReal ((a : ℝ) / c) ≤ I) :
    ENNReal.ofReal (((max a 0 : ℤ) : ℝ) / c) ≤ I := by
  rcases le_total 0 a with ha | ha
  · rwa [max_eq_left ha]
  · rw [max_eq_right ha]; simp

/-- Soundness of the recursion, for every decision function. -/
theorem bnbExact_sound {k : ℕ} {L : List ℤ → List ℤ → ℤ} (hL : LeafSoundProp k L)
    (dec : List ℤ → List ℤ → Dec) (fuel : ℕ) (lo hi : List ℤ) :
    ENNReal.ofReal ((bnbExact k dec L fuel lo hi : ℝ) / 2 ^ OS) ≤
      ∫⁻ x in boxOf lo hi ∩ Dk k, F2 k x := by
  by_cases hl : lo.length = mDim k
  swap
  · rw [bnbExact_length k dec L fuel lo hi hl]; simp
  induction fuel generalizing lo hi with
  | zero => simp [bnbExact]
  | succ n ih =>
    simp only [bnbExact]
    split
    · rename_i d _
      split_ifs with hd
      · set mid := (lo.getD d 0 + hi.getD d 0) / 2 with hmid
        have h1 := ih lo (hi.set d mid) hl
        have h2 := ih (lo.set d mid) hi (by simpa using hl)
        have hdm : d < mDim k := hl ▸ hd.1
        have hdisj := boxOf_halves_disjoint (m := mDim k) lo hi d mid hdm hd.1 hd.2
        calc ENNReal.ofReal (((bnbExact k dec L n lo (hi.set d mid) +
                bnbExact k dec L n (lo.set d mid) hi : ℤ) : ℝ) / 2 ^ OS)
            ≤ ENNReal.ofReal ((bnbExact k dec L n lo (hi.set d mid) : ℝ) / 2 ^ OS) +
                ENNReal.ofReal ((bnbExact k dec L n (lo.set d mid) hi : ℝ) / 2 ^ OS) := by
              rw [Int.cast_add, add_div]; exact ENNReal.ofReal_add_le
          _ ≤ (∫⁻ x in boxOf lo (hi.set d mid) ∩ Dk k, F2 k x) +
                ∫⁻ x in boxOf (lo.set d mid) hi ∩ Dk k, F2 k x := add_le_add h1 h2
          _ = ∫⁻ x in (boxOf lo (hi.set d mid) ∩ Dk k) ∪ (boxOf (lo.set d mid) hi ∩ Dk k), F2 k x := by
              rw [lintegral_union ((measurableSet_boxOf _ _).inter (measurableSet_Dk k))
                (hdisj.mono inter_subset_left inter_subset_left)]
          _ ≤ ∫⁻ x in boxOf lo hi ∩ Dk k, F2 k x :=
              lintegral_mono_set (union_subset
                (inter_subset_inter_left _ (boxOf_lower_subset lo hi d))
                (inter_subset_inter_left _ (boxOf_upper_subset lo hi d)))
      · simp
    · split_ifs with hv
      · exact ofReal_max_div_le (by positivity) (hL lo hi (validB_valid hv))
      · simp
    · simp

/-! ## the initial boxes -/

lemma foldl_inv {α β : Type*} (P : β → Prop) (f : β → α → β) :
    ∀ (l : List α) (b : β), P b → (∀ b, ∀ a ∈ l, P b → P (f b a)) → P (l.foldl f b)
  | [], _, hb, _ => hb
  | a :: l, b, hb, hf =>
    foldl_inv P f l (f b a) (hf b a (by simp) hb) (fun b' a' ha' hb' => hf b' a' (by simp [ha']) hb')

lemma widest_lt (lo hi : List ℤ) (h : 0 < lo.length) : widest lo hi < lo.length := by
  unfold widest
  apply foldl_inv (fun best : ℕ × ℤ => best.1 < lo.length)
  · exact h
  · intro b a ha hb
    simp only [List.mem_range] at ha
    dsimp only
    split_ifs
    · exact ha
    · exact hb

lemma initBoxGo_length (t : ℕ) : ∀ r (lo hi : List ℤ),
    (initBoxGo t r lo hi).1.length = lo.length ∧ (initBoxGo t r lo hi).2.length = hi.length
  | 0, _, _ => ⟨rfl, rfl⟩
  | r + 1, lo, hi => by
    simp only [initBoxGo]
    split_ifs
    · have := initBoxGo_length t r (lo.set (widest lo hi) ((lo.getD (widest lo hi) 0 +
        hi.getD (widest lo hi) 0) / 2)) hi
      simpa using this
    · have := initBoxGo_length t r lo (hi.set (widest lo hi) ((lo.getD (widest lo hi) 0 +
        hi.getD (widest lo hi) 0) / 2))
      simpa using this

lemma initBoxGo_subset {m : ℕ} (t : ℕ) : ∀ r (lo hi : List ℤ),
    (boxOf (initBoxGo t r lo hi).1 (initBoxGo t r lo hi).2 : Set (Fin m → ℝ)) ⊆ boxOf lo hi
  | 0, _, _ => subset_refl _
  | r + 1, lo, hi => by
    simp only [initBoxGo]
    split_ifs
    · exact (initBoxGo_subset t r _ _).trans (boxOf_upper_subset lo hi _)
    · exact (initBoxGo_subset t r _ _).trans (boxOf_lower_subset lo hi _)

lemma initBoxGo_disjoint {m : ℕ} (t t' : ℕ) : ∀ r (lo hi : List ℤ), lo.length = m → hi.length = m →
    0 < m → (∃ i < r, t.testBit i ≠ t'.testBit i) →
    Disjoint (boxOf (initBoxGo t r lo hi).1 (initBoxGo t r lo hi).2 : Set (Fin m → ℝ))
      (boxOf (initBoxGo t' r lo hi).1 (initBoxGo t' r lo hi).2)
  | 0, _, _, _, _, _, ⟨i, hir, _⟩ => absurd hir (Nat.not_lt_zero _)
  | r + 1, lo, hi, hlo, hhi, hm, ⟨i, hir, hne⟩ => by
    simp only [initBoxGo]
    have hd : widest lo hi < m := hlo ▸ widest_lt lo hi (hlo ▸ hm)
    by_cases hb : t.testBit r = t'.testBit r
    · have hir' : i < r := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hir with h | h
        · exact h
        · exact absurd (h ▸ hb) hne
      rw [hb]
      split_ifs
      · exact initBoxGo_disjoint t t' r _ _ (by simp [hlo]) hhi hm ⟨i, hir', hne⟩
      · exact initBoxGo_disjoint t t' r _ _ hlo (by simp [hhi]) hm ⟨i, hir', hne⟩
    · have hdis := boxOf_halves_disjoint (m := m) lo hi (widest lo hi)
        ((lo.getD (widest lo hi) 0 + hi.getD (widest lo hi) 0) / 2) hd (hlo ▸ hd) (hhi ▸ hd)
      cases ht : t.testBit r <;> cases ht' : t'.testBit r <;> simp only [ht, ht'] at hb ⊢
      · simp at hb
      · exact (hdis.mono (initBoxGo_subset t r _ _) (initBoxGo_subset t' r _ _))
      · exact (hdis.mono (initBoxGo_subset t' r _ _) (initBoxGo_subset t r _ _)).symm
      · simp at hb

theorem initBox_subset (k R t : ℕ) :
    (boxOf (initBox k R t).1 (initBox k R t).2 : Set (Fin (mDim k) → ℝ)) ⊆ Xk k := by
  rw [← boxOf_root k]
  exact initBoxGo_subset t R _ _

theorem initBox_disjoint {k R t t' : ℕ} (hk : 2 ≤ k) (ht : t < 2 ^ R) (ht' : t' < 2 ^ R) (hne : t ≠ t') :
    Disjoint (boxOf (initBox k R t).1 (initBox k R t).2 : Set (Fin (mDim k) → ℝ))
      (boxOf (initBox k R t').1 (initBox k R t').2) := by
  apply initBoxGo_disjoint t t' R _ _ (rootLo_length k) (rootHi_length k) (by unfold mDim; omega)
  by_contra hcon
  push Not at hcon
  apply hne
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < R
  · exact hcon i hi
  · have h2 : 2 ^ R ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ht h2), Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ht' h2)]

/-! ## shards -/

lemma foldl_add_range (f : ℕ → ℤ) : ∀ (n : ℕ) (c : ℤ),
    (List.range n).foldl (fun acc i => acc + f i) c = c + ∑ i ∈ Finset.range n, f i
  | 0, c => by simp
  | n + 1, c => by
    rw [List.range_succ, List.foldl_append, foldl_add_range f n c, Finset.sum_range_succ]
    simp [add_assoc]

/-- the tree of the initial box `t` -/
def treeVal (k : ℕ) (dec : List ℤ → List ℤ → Dec) (L : List ℤ → List ℤ → ℤ) (R t : ℕ) : ℤ :=
  bnbExact k dec L FUEL (initBox k R t).1 (initBox k R t).2

lemma shardSum_eq_sum (k : ℕ) (dec : List ℤ → List ℤ → Dec) (L : List ℤ → List ℤ → ℤ) (R a b : ℕ) :
    shardSum k dec L R a b = ∑ i ∈ Finset.range (b - a), treeVal k dec L R (a + i) := by
  unfold shardSum
  rw [← zero_add (∑ i ∈ Finset.range (b - a), treeVal k dec L R (a + i)),
    ← foldl_add_range (fun i => treeVal k dec L R (a + i))]
  rfl

theorem shardSum_add (k : ℕ) (dec : List ℤ → List ℤ → Dec) (L : List ℤ → List ℤ → ℤ) {R a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    shardSum k dec L R a b + shardSum k dec L R b c = shardSum k dec L R a c := by
  rw [shardSum_eq_sum, shardSum_eq_sum, shardSum_eq_sum]
  have e : c - a = (b - a) + (c - b) := by omega
  rw [e, Finset.sum_range_add]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  omega

theorem shardSum_nonneg (k : ℕ) (dec : List ℤ → List ℤ → Dec) (L : List ℤ → List ℤ → ℤ) (R a b : ℕ) :
    0 ≤ shardSum k dec L R a b := by
  rw [shardSum_eq_sum]
  exact Finset.sum_nonneg fun i _ => bnbExact_nonneg k dec L _ _ _

/-- Soundness of a shard: for every decision function. -/
theorem shardSum_sound {k : ℕ} (hk : 2 ≤ k) {L : List ℤ → List ℤ → ℤ} (hL : LeafSoundProp k L)
    (dec : List ℤ → List ℤ → Dec) {R a b : ℕ} (hb : b ≤ 2 ^ R) :
    ENNReal.ofReal ((shardSum k dec L R a b : ℝ) / 2 ^ OS) ≤ ∫⁻ x in Dk k ∩ Xk k, F2 k x := by
  set B : ℕ → Set (Fin (mDim k) → ℝ) := fun i => boxOf (initBox k R (a + i)).1 (initBox k R (a + i)).2
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (b - a))) fun i => B i ∩ Dk k := by
    intro i hi j hj hij
    simp only [Finset.coe_range, mem_Iio] at hi hj
    exact (initBox_disjoint hk (by omega) (by omega) (by omega)).mono inter_subset_left inter_subset_left
  calc ENNReal.ofReal ((shardSum k dec L R a b : ℝ) / 2 ^ OS)
      = ∑ i ∈ Finset.range (b - a), ENNReal.ofReal ((treeVal k dec L R (a + i) : ℝ) / 2 ^ OS) := by
        rw [shardSum_eq_sum, Int.cast_sum, Finset.sum_div]
        exact ENNReal.ofReal_sum_of_nonneg fun i _ =>
          div_nonneg (by exact_mod_cast bnbExact_nonneg k dec L _ _ _) (by positivity)
    _ ≤ ∑ i ∈ Finset.range (b - a), ∫⁻ x in B i ∩ Dk k, F2 k x :=
        Finset.sum_le_sum fun i _ => bnbExact_sound hL dec _ _ _
    _ = ∫⁻ x in ⋃ i ∈ Finset.range (b - a), B i ∩ Dk k, F2 k x :=
        (lintegral_biUnion_finset hdisj (fun i _ => (measurableSet_boxOf _ _).inter (measurableSet_Dk k)) _).symm
    _ ≤ ∫⁻ x in Dk k ∩ Xk k, F2 k x := by
        apply lintegral_mono_set
        intro x hx
        simp only [mem_iUnion, mem_inter_iff] at hx
        obtain ⟨i, _, hxB, hxD⟩ := hx
        exact ⟨hxD, initBox_subset k R (a + i) hxB⟩

end BHH.E

namespace BHH

-- the deliverables of this file, also under `BHH` (helpers stay in `BHH.E`)
export E (validB_valid bnbExact_nonneg bnbExact_sound initBox_subset initBox_disjoint treeVal shardSum_eq_sum shardSum_add shardSum_nonneg shardSum_sound)

end BHH
