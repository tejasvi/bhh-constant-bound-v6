/-
The exact recursion of a run unrolls to the discrete bound: `Clx i = Ψ^d` with `i + 2` increments (`Psid`), for the
table data `discOf` of the run.  The recursion sums over cell sequences with the pass run as a finite automaton on
its 17 reachable states; the tables `mkPassTab` are checked by kernel evaluation.
-/
import W2.RunSound
import W2.Defs

open Real

namespace BHH.W2

open W2C BHH.Cert BHH

/-! ## The pass table -/

/-- The state index of an optional state (`17` for `none`). -/
def sIdx : Option St → ℕ
  | none => 17
  | some s => stIndex s

lemma sIdx_none : sIdx none = 17 := rfl
lemma sIdx_some (s : St) : sIdx (some s) = stIndex s := rfl

/-- The reachable state with index `s`. -/
def stOf (s : ℕ) : St := reachable.getD s default

/-- `s` is a reachable state, with its index. -/
def Good (s : St) : Prop := stIndex s < 17 ∧ stOf (stIndex s) = s

lemma trans_eq : ∀ s : Fin 17, ∀ a1 a2 : Bool,
    mkPassTab.trans[(s.val * 2 + b2n a1) * 2 + b2n a2]! = sIdx ((stOf s.val).step a1 a2) := by
  decide +kernel

lemma close2_tab_eq : ∀ s : Fin 17, ∀ a1 a2 : Bool,
    mkPassTab.close2[(s.val * 2 + b2n a1) * 2 + b2n a2]! = (stOf s.val).closeStep2 a1 a2 := by
  decide +kernel

lemma init1_eq : ∀ a1 : Bool, mkPassTab.init1[b2n a1]! = sIdx (St.init.step a1 false) := by
  decide +kernel

lemma init_step_a2 : ∀ a1 a2 : Bool, St.init.step a1 a2 = St.init.step a1 false := by decide +kernel

lemma good_init : Good St.init := by unfold Good; decide +kernel

/-- `s` is reachable with its index (as a `Bool`). -/
def goodB (s : St) : Bool := decide (stIndex s < 17 ∧ stOf (stIndex s) = s)

lemma reach_closed_dec : ∀ s : Fin 17, ∀ a1 a2 : Bool, ((stOf s.val).step a1 a2).all goodB = true := by
  decide +kernel

lemma good_step {s s' : St} (hs : Good s) {a1 a2 : Bool} (h : s.step a1 a2 = some s') : Good s' := by
  have hc := reach_closed_dec ⟨stIndex s, hs.1⟩ a1 a2
  simp only [hs.2, h, Option.all_some, goodB, decide_eq_true_eq] at hc
  exact hc

lemma good_runPass (a1 a2 : ℕ → Bool) : ∀ n s, runPass a1 a2 n = some s → Good s
  | 0, s, h => by
    simp only [runPass, Option.some.injEq] at h
    rw [← h]; exact good_init
  | n + 1, s, h => by
    simp only [runPass] at h
    cases hr : runPass a1 a2 n with
    | none => rw [hr] at h; simp at h
    | some s0 =>
      rw [hr] at h
      simp only [Option.bind_some] at h
      exact good_step (good_runPass a1 a2 n s0 hr) h

lemma stOf_stIndex {s : St} (hs : Good s) : stOf (stIndex s) = s := hs.2

/-- The closing value of an optional state (twice `Λ`, `0` for `none`). -/
def closeVal : Option St → ℕ
  | none => 0
  | some s => s.close2

lemma passVal2_eq (a1 a2 : ℕ → Bool) (k : ℕ) : passVal2 a1 a2 k = closeVal (runPass a1 a2 (k - 1)) := by
  unfold passVal2
  cases runPass a1 a2 (k - 1) <;> rfl

/-- The closing value of an optional state after one more point, through the table. -/
lemma close_opt (o : Option St) (ho : ∀ s, o = some s → Good s) (a1 a2 : Bool) :
    (closeVal (o.bind (fun s => s.step a1 a2)) : ℝ) =
      ∑ D ∈ Finset.range 17, if sIdx o = D then (mkPassTab.close2[(D * 2 + b2n a1) * 2 + b2n a2]! : ℝ) else 0 := by
  cases o with
  | none =>
    simp only [Option.bind_none, closeVal, Nat.cast_zero]
    symm
    apply Finset.sum_eq_zero
    intro D hD
    rw [Finset.mem_range] at hD
    have hne : sIdx none ≠ D := by rw [sIdx_none]; omega
    rw [if_neg hne]
  | some s =>
    have hs := ho s rfl
    rw [Option.bind_some, sIdx_some]
    rw [Finset.sum_ite_eq (Finset.range 17) (stIndex s), if_pos (Finset.mem_range.mpr hs.1)]
    rw [close2_tab_eq ⟨stIndex s, hs.1⟩ a1 a2]
    simp only [stOf_stIndex hs, St.closeStep2]
    cases s.step a1 a2 <;> rfl

/-- The transition of an optional state, through the table. -/
lemma trans_opt (o : Option St) (ho : ∀ s, o = some s → Good s) (a1 a2 : Bool) {D2 : ℕ} (hD2 : D2 < 17)
    (v : ℝ) :
    (if sIdx (o.bind (fun s => s.step a1 a2)) = D2 then v else 0) =
      ∑ D ∈ Finset.range 17,
        if sIdx o = D then (if mkPassTab.trans[(D * 2 + b2n a1) * 2 + b2n a2]! = D2 then v else 0) else 0 := by
  cases o with
  | none =>
    simp only [Option.bind_none]
    have h17 : sIdx none ≠ D2 := by rw [sIdx_none]; omega
    rw [if_neg h17]
    symm
    apply Finset.sum_eq_zero
    intro D hD
    rw [Finset.mem_range] at hD
    have hne : sIdx none ≠ D := by rw [sIdx_none]; omega
    rw [if_neg hne]
  | some s =>
    have hs := ho s rfl
    rw [Option.bind_some, sIdx_some]
    rw [Finset.sum_ite_eq (Finset.range 17) (stIndex s), if_pos (Finset.mem_range.mpr hs.1)]
    rw [trans_eq ⟨stIndex s, hs.1⟩ a1 a2, stOf_stIndex hs]

/-! ## Cell sequences -/

/-- Sum over `n+1`-tuples by the last entry. -/
lemma sum_snoc {α : Type*} [Fintype α] {n : ℕ} (F : (Fin (n + 1) → α) → ℝ) :
    ∑ c, F c = ∑ c' : Fin n → α, ∑ x : α, F (Fin.snoc c' x) := by
  rw [← (Fin.snocEquiv (fun _ => α)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

section Seq

variable {g : GridR} (hNR : 0 < g.NR) (hNT : 0 < g.NT) (D : DiscData)

/-- A cell. -/
abbrev Cell (g : GridR) := Fin g.NR × Fin g.NT

/-- Append a cell. -/
def csnoc {n : ℕ} (c : CellSeq g n) (x : Cell g) : CellSeq g (n + 1) := Fin.snoc (α := fun _ => Cell g) c x

lemma cget_csnoc_lt {n : ℕ} (c : CellSeq g n) (x : Cell g) {j : ℕ} (hj : j < n) :
    cget hNR hNT (csnoc c x) j = cget hNR hNT c j := by
  unfold cget csnoc
  rw [dif_pos (by omega : j < n + 1), dif_pos hj]
  have e : (⟨j, by omega⟩ : Fin (n + 1)) = Fin.castSucc ⟨j, hj⟩ := rfl
  rw [e, Fin.snoc_castSucc]

lemma cget_csnoc_last {n : ℕ} (c : CellSeq g n) (x : Cell g) : cget hNR hNT (csnoc c x) n = x := by
  unfold cget csnoc
  rw [dif_pos (Nat.lt_succ_self n)]
  have e : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n := rfl
  rw [e, Fin.snoc_last]

lemma edgeA1_csnoc {n : ℕ} (c : CellSeq g n) (x : Cell g) {j : ℕ} (hj : j ≤ n) :
    edgeA1 hNR hNT D (csnoc c x) j = edgeA1 hNR hNT D c j := by
  unfold edgeA1
  split_ifs with h1
  · rw [cget_csnoc_lt hNR hNT c x (by omega)]
  · rfl

lemma edgeA1_csnoc_last {n : ℕ} (c : CellSeq g n) (x : Cell g) :
    edgeA1 hNR hNT D (csnoc c x) (n + 1) = D.nf x.1.val := by
  unfold edgeA1
  rw [if_pos (by omega), Nat.add_sub_cancel, cget_csnoc_last]

lemma edgeA2_csnoc {n : ℕ} (c : CellSeq g n) (x : Cell g) {j : ℕ} (hj : j ≤ n) :
    edgeA2 hNR hNT D (csnoc c x) j = edgeA2 hNR hNT D c j := by
  unfold edgeA2
  split_ifs with h1
  · rw [cget_csnoc_lt hNR hNT c x (by omega), cget_csnoc_lt hNR hNT c x (by omega)]
  · rfl

lemma edgeA2_csnoc_last {n : ℕ} (hn : 1 ≤ n) (c : CellSeq g n) (x : Cell g) :
    edgeA2 hNR hNT D (csnoc c x) (n + 1) =
      D.sc (cget hNR hNT c (n - 1)).1.val x.1.val (doff (cget hNR hNT c (n - 1)) x) := by
  unfold edgeA2
  rw [if_pos (by omega)]
  have e1 : n + 1 - 2 = n - 1 := by omega
  have e2 : n + 1 - 1 = n := by omega
  simp only [e1, e2]
  rw [cget_csnoc_lt hNR hNT c x (by omega), cget_csnoc_last]

lemma edgeA2_one {n : ℕ} (c : CellSeq g n) : edgeA2 hNR hNT D c 1 = false := by
  unfold edgeA2; rw [if_neg (by omega)]

lemma runPass_congr {a1 a2 b1 b2 : ℕ → Bool} :
    ∀ i, (∀ j, 1 ≤ j → j ≤ i → a1 j = b1 j ∧ a2 j = b2 j) → runPass a1 a2 i = runPass b1 b2 i
  | 0, _ => rfl
  | i + 1, h => by
    simp only [runPass]
    rw [runPass_congr i (fun j h1 h2 => h j h1 (by omega)), (h (i + 1) (by omega) le_rfl).1,
      (h (i + 1) (by omega) le_rfl).2]

/-- The pass state after the points `0, ..., m` of a sequence of `m` increments. -/
def seqRun {m : ℕ} (c : CellSeq g m) : Option St := runPass (edgeA1 hNR hNT D c) (edgeA2 hNR hNT D c) m

lemma seqRun_csnoc {n : ℕ} (c : CellSeq g n) (x : Cell g) :
    seqRun hNR hNT D (csnoc c x) =
      (seqRun hNR hNT D c).bind fun s => s.step (D.nf x.1.val) (edgeA2 hNR hNT D (csnoc c x) (n + 1)) := by
  unfold seqRun
  simp only [runPass]
  rw [edgeA1_csnoc_last, runPass_congr n (fun j _ hj => ⟨edgeA1_csnoc hNR hNT D c x hj,
    edgeA2_csnoc hNR hNT D c x hj⟩)]

lemma seqRun_good {m : ℕ} (c : CellSeq g m) : ∀ s, seqRun hNR hNT D c = some s → Good s :=
  good_runPass _ _ m

lemma prod_csnoc {n : ℕ} (c : CellSeq g n) (x : Cell g) :
    ∏ j, D.w ((csnoc c x) j).1.val = (∏ j, D.w (c j).1.val) * D.w x.1.val := by
  rw [Fin.prod_univ_castSucc]
  simp only [csnoc, Fin.snoc_castSucc, Fin.snoc_last]

lemma expoSeq_csnoc {n : ℕ} (hn : 1 ≤ n) (c : CellSeq g n) (x : Cell g) :
    expoSeq hNR hNT D (csnoc c x) = expoSeq hNR hNT D c +
      D.ab (cget hNR hNT c (n - 1)).1.val x.1.val (doff (cget hNR hNT c (n - 1)) x) := by
  unfold expoSeq
  rw [cget_csnoc_lt hNR hNT c x (by omega), Finset.sum_Ico_succ_top (by omega : 1 ≤ n), add_assoc]
  congr 1
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Ico] at hj
    rw [cget_csnoc_lt hNR hNT c x (by omega), cget_csnoc_lt hNR hNT c x (by omega)]
  · rw [cget_csnoc_lt hNR hNT c x (by omega), cget_csnoc_last]

lemma expoSeq_csnoc_zero (c : CellSeq g 0) (x : Cell g) :
    expoSeq hNR hNT D (csnoc c x) = D.ub x.1.val := by
  unfold expoSeq
  rw [cget_csnoc_last]
  simp

/-! ## Path sums -/

variable (t : ℝ)

/-- The weight `Π_j w(c_j) e^{-t (exponent bound)}` of a cell sequence. -/
noncomputable def seqWt {m : ℕ} (c : CellSeq g m) : ℝ :=
  (∏ j, D.w (c j).1.val) * Real.exp (-(t * expoSeq hNR hNT D c))

/-- The path sum: sequences of `n + 1` cells ending in `x` whose pass is in the state with index `s`. -/
noncomputable def Phi (n : ℕ) (x : Cell g) (s : ℕ) : ℝ :=
  ∑ c : CellSeq g (n + 1),
    if cget hNR hNT c n = x ∧ sIdx (seqRun hNR hNT D c) = s then seqWt hNR hNT D t c else 0

lemma Phi_zero (x : Cell g) (s : ℕ) :
    Phi hNR hNT D t 0 x s =
      if sIdx (St.init.step (D.nf x.1.val) false) = s then D.w x.1.val * Real.exp (-(t * D.ub x.1.val)) else 0 := by
  unfold Phi
  rw [sum_snoc]
  rw [Fintype.sum_unique]
  change ∑ y : Cell g, _ = _
  rw [Finset.sum_eq_single x]
  · rw [show (default : CellSeq g 0) = (default : CellSeq g 0) from rfl]
    have hc : Fin.snoc (α := fun _ => Cell g) (default : CellSeq g 0) x = csnoc default x := rfl
    rw [hc, cget_csnoc_last, seqRun_csnoc, edgeA2_one]
    simp only [true_and]
    unfold seqWt
    rw [prod_csnoc, expoSeq_csnoc_zero]
    simp [seqRun, runPass]
  · intro y _ hy
    have hc : Fin.snoc (α := fun _ => Cell g) (default : CellSeq g 0) y = csnoc default y := rfl
    rw [hc, cget_csnoc_last, if_neg (fun h => hy h.1)]
  · intro h; exact absurd (Finset.mem_univ x) h

lemma Phi_succ (n : ℕ) (x2 : Cell g) {s2 : ℕ} (hs2 : s2 < 17) :
    Phi hNR hNT D t (n + 1) x2 s2 =
      ∑ x : Cell g, ∑ s ∈ Finset.range 17,
        (if mkPassTab.trans[(s * 2 + b2n (D.nf x2.1.val)) * 2 + b2n (D.sc x.1.val x2.1.val (doff x x2))]! = s2
          then D.w x2.1.val * Real.exp (-(t * D.ab x.1.val x2.1.val (doff x x2))) else 0) *
          Phi hNR hNT D t n x s := by
  unfold Phi
  rw [sum_snoc]
  -- collapse the last cell to `x2`
  have h1 : ∀ c' : CellSeq g (n + 1),
      (∑ y : Cell g, if cget hNR hNT (Fin.snoc (α := fun _ => Cell g) c' y) (n + 1) = x2 ∧
          sIdx (seqRun hNR hNT D (Fin.snoc (α := fun _ => Cell g) c' y)) = s2
        then seqWt hNR hNT D t (Fin.snoc (α := fun _ => Cell g) c' y) else 0) =
      ∑ x : Cell g, ∑ s ∈ Finset.range 17,
        if cget hNR hNT c' n = x ∧ sIdx (seqRun hNR hNT D c') = s then
          (if mkPassTab.trans[(s * 2 + b2n (D.nf x2.1.val)) * 2 + b2n (D.sc x.1.val x2.1.val (doff x x2))]! = s2
            then D.w x2.1.val * Real.exp (-(t * D.ab x.1.val x2.1.val (doff x x2))) else 0) *
            seqWt hNR hNT D t c'
        else 0 := by
    intro c'
    rw [Finset.sum_eq_single x2]
    · have hc : Fin.snoc (α := fun _ => Cell g) c' x2 = csnoc c' x2 := rfl
      rw [hc, cget_csnoc_last, seqRun_csnoc, edgeA2_csnoc_last hNR hNT D (by omega)]
      simp only [true_and, Nat.add_sub_cancel]
      rw [Finset.sum_eq_single (cget hNR hNT c' n)]
      · simp only [true_and]
        have hw : seqWt hNR hNT D t (csnoc c' x2) =
            D.w x2.1.val * Real.exp (-(t * D.ab (cget hNR hNT c' n).1.val x2.1.val
              (doff (cget hNR hNT c' n) x2))) * seqWt hNR hNT D t c' := by
          unfold seqWt
          rw [prod_csnoc, expoSeq_csnoc hNR hNT D (by omega), Nat.add_sub_cancel]
          rw [mul_add, neg_add, Real.exp_add]
          ring
        rw [hw, trans_opt _ (seqRun_good hNR hNT D c') _ _ hs2]
        apply Finset.sum_congr rfl
        intro s _
        by_cases hs : sIdx (seqRun hNR hNT D c') = s
        · rw [if_pos hs, if_pos hs]
          split_ifs <;> simp
        · rw [if_neg hs, if_neg hs]
      · intro x _ hx
        apply Finset.sum_eq_zero
        intro s _
        rw [if_neg (fun h => hx h.1.symm)]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro y _ hy
      have hc : Fin.snoc (α := fun _ => Cell g) c' y = csnoc c' y := rfl
      rw [hc, cget_csnoc_last, if_neg (fun h => hy h.1)]
    · intro h; exact absurd (Finset.mem_univ x2) h
  rw [Finset.sum_congr rfl (fun c' _ => h1 c'), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c' _
  split_ifs <;> ring


/-- Collapse a sum over cells and states to the cell `x0`. -/
lemma sum_collapse {β : Type*} [Fintype β] [DecidableEq β] (x0 : β) (P : ℕ → Prop) [DecidablePred P]
    (F : β → ℕ → ℝ) :
    (∑ x : β, ∑ s ∈ Finset.range 17, if x0 = x ∧ P s then F x s else 0) =
      ∑ s ∈ Finset.range 17, if P s then F x0 s else 0 := by
  rw [Finset.sum_eq_single x0]
  · simp only [true_and]
  · intro x _ hx
    apply Finset.sum_eq_zero
    intro s _
    rw [if_neg (fun h => hx h.1.symm)]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `Ψ^d` with `n + 2` increments through the path sums of `n + 1` cells. -/
lemma Psid_eq_Phi (n : ℕ) :
    Psid g hNR hNT D (n + 2) t =
      (1 / 2) * ∑ x2 : Cell g, ∑ x : Cell g, ∑ s ∈ Finset.range 17,
        ((mkPassTab.close2[(s * 2 + b2n (D.nf x2.1.val)) * 2 + b2n (D.sc x.1.val x2.1.val (doff x x2))]! : ℝ) *
          (D.w x2.1.val * Real.exp (-(t * D.ab x.1.val x2.1.val (doff x x2))))) * Phi hNR hNT D t n x s := by
  unfold Psid
  rw [sum_snoc]
  have h1 : ∀ (c' : CellSeq g (n + 1)) (x2 : Cell g),
      (passVal2 (edgeA1 hNR hNT D (Fin.snoc (α := fun _ => Cell g) c' x2))
          (edgeA2 hNR hNT D (Fin.snoc (α := fun _ => Cell g) c' x2)) (n + 2 + 1) : ℝ) / 2 *
          (∏ j, D.w ((Fin.snoc (α := fun _ => Cell g) c' x2) j).1.val) *
          Real.exp (-(t * expoSeq hNR hNT D (Fin.snoc (α := fun _ => Cell g) c' x2))) =
        (1 / 2) * ∑ x : Cell g, ∑ s ∈ Finset.range 17,
          if cget hNR hNT c' n = x ∧ sIdx (seqRun hNR hNT D c') = s then
            ((mkPassTab.close2[(s * 2 + b2n (D.nf x2.1.val)) * 2 +
                b2n (D.sc x.1.val x2.1.val (doff x x2))]! : ℝ) *
              (D.w x2.1.val * Real.exp (-(t * D.ab x.1.val x2.1.val (doff x x2))))) * seqWt hNR hNT D t c'
          else 0 := by
    intro c' x2
    have hc : Fin.snoc (α := fun _ => Cell g) c' x2 = csnoc c' x2 := rfl
    rw [hc]
    have hpv : passVal2 (edgeA1 hNR hNT D (csnoc c' x2)) (edgeA2 hNR hNT D (csnoc c' x2)) (n + 2 + 1) =
        closeVal ((seqRun hNR hNT D c').bind (fun s => s.step (D.nf x2.1.val)
          (D.sc (cget hNR hNT c' n).1.val x2.1.val (doff (cget hNR hNT c' n) x2)))) := by
      rw [passVal2_eq]
      have := seqRun_csnoc hNR hNT D c' x2
      unfold seqRun at this
      rw [show n + 2 + 1 - 1 = n + 1 + 1 by omega, this, edgeA2_csnoc_last hNR hNT D (by omega),
        Nat.add_sub_cancel]
      rfl
    have hw : (∏ j, D.w ((csnoc c' x2) j).1.val) * Real.exp (-(t * expoSeq hNR hNT D (csnoc c' x2))) =
        D.w x2.1.val * Real.exp (-(t * D.ab (cget hNR hNT c' n).1.val x2.1.val (doff (cget hNR hNT c' n) x2))) *
          seqWt hNR hNT D t c' := by
      unfold seqWt
      rw [prod_csnoc, expoSeq_csnoc hNR hNT D (by omega), Nat.add_sub_cancel, mul_add, neg_add, Real.exp_add]
      ring
    rw [hpv, close_opt _ (seqRun_good hNR hNT D c'), mul_assoc, hw]
    rw [sum_collapse (cget hNR hNT c' n) (fun s => sIdx (seqRun hNR hNT D c') = s)
      (fun x s => ((mkPassTab.close2[(s * 2 + b2n (D.nf x2.1.val)) * 2 +
          b2n (D.sc x.1.val x2.1.val (doff x x2))]! : ℝ) *
        (D.w x2.1.val * Real.exp (-(t * D.ab x.1.val x2.1.val (doff x x2))))) * seqWt hNR hNT D t c')]
    rw [Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun c' _ => Finset.sum_congr rfl (fun x2 _ => h1 c' x2)), Finset.sum_comm,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x2 _
  rw [← Finset.mul_sum]
  congr 1
  unfold Phi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c' _
  split_ifs <;> ring

end Seq

lemma sum_range_cells (g : GridR) (f : ℕ → ℝ) :
    ∑ c ∈ Finset.range (g.NR * g.NT), f c = ∑ x : Cell g, f (x.1.val * g.NT + x.2.val) := by
  rw [Finset.sum_range]
  rw [← (finProdFinEquiv (m := g.NR) (n := g.NT)).sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  simp only [finProdFinEquiv_apply_val]
  congr 1
  ring

lemma flat_div {NT : ℕ} (a b : ℕ) (hb : b < NT) : (a * NT + b) / NT = a := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hb, zero_add]

lemma flat_mod {NT : ℕ} (a b : ℕ) (hb : b < NT) : (a * NT + b) % NT = b := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

lemma q_div {c s : ℕ} (hs : s < 17) : (c * 17 + s) / 17 = c := flat_div c s hs
lemma q_mod {c s : ℕ} (hs : s < 17) : (c * 17 + s) % 17 = s := flat_mod c s hs

lemma toNat_off (a b N : ℕ) (hb : b < N) : (((a : ℤ) - b) + ((N - 1 : ℕ) : ℤ)).toNat = a + (N - 1) - b := by
  omega

lemma b2n_div (a b : Bool) : (b2n a * 2 + b2n b) / 2 = b2n a := by cases a <;> cases b <;> rfl
lemma b2n_mod (a b : Bool) : (b2n a * 2 + b2n b) % 2 = b2n b := by cases a <;> cases b <;> rfl

/-! ## Unrolling, for exact data matching table data -/

section Gen

variable {g : GridR} (hNR : 0 < g.NR) (hNT : 0 < g.NT) (D : DiscData) (t : ℝ) (X : ExData)

/-- The exact data `X` of a recursion and the table data `D` describe the same tables (cells flat-indexed
`ir * NT + it`). -/
structure Match (g : GridR) (D : DiscData) (t : ℝ) (X : ExData) : Prop where
  NT : X.NT = g.NT
  NC : X.NC = g.NR * g.NT
  pt : X.pt = mkPassTab
  t : X.t = t
  w : ∀ ir, X.wR ir = D.w ir
  ub : ∀ ir, X.ubR ir = D.ub ir
  nb : ∀ ir : Fin g.NR, X.nb[ir.val]! = b2n (D.nf ir.val)
  ab : ∀ x x2 : Cell g, X.abR (idxOf X.NR X.NT X.ND x2.1.val x2.2.val (x.1.val * g.NT + x.2.val)) =
    D.ab x.1.val x2.1.val (doff x x2)
  ns : ∀ x x2 : Cell g, X.nsOf (x2.1.val * g.NT + x2.2.val) (x.1.val * g.NT + x.2.val) =
    b2n (D.nf x2.1.val) * 2 + b2n (D.sc x.1.val x2.1.val (doff x x2))

variable {D t X}

theorem RxF_eq_Phi (hm : Match g D t X) : ∀ (i : ℕ) (x : Cell g) (s : ℕ), s < 17 →
    X.RxF i ((x.1.val * g.NT + x.2.val) * 17 + s) = Phi hNR hNT D t i x s := by
  intro i
  induction i with
  | zero =>
    intro x s hs
    rw [Phi_zero]
    have hq : (x.1.val * g.NT + x.2.val) * 17 + s < X.NC * 17 := by
      rw [hm.NC]; nlinarith [x.1.isLt, x.2.isLt]
    have hdiv : ((x.1.val * g.NT + x.2.val) * 17 + s) / 17 / X.NT = x.1.val := by
      rw [q_div hs, hm.NT, flat_div _ _ x.2.isLt]
    simp only [ExData.RxF]
    rw [hdiv, q_mod hs, hm.pt, hm.nb x.1, init1_eq, hm.w, hm.ub, hm.t]
    exact if_congr ⟨fun h => h.2, fun h => ⟨hq, h⟩⟩ rfl rfl
  | succ i ih =>
    intro x2 s2 hs2
    rw [Phi_succ _ _ _ _ _ _ hs2]
    have hq : (x2.1.val * g.NT + x2.2.val) * 17 + s2 < X.NC * 17 := by
      rw [hm.NC]; nlinarith [x2.1.isLt, x2.2.isLt]
    have hA : (x2.1.val * g.NT + x2.2.val) / X.NT = x2.1.val := by rw [hm.NT, flat_div _ _ x2.2.isLt]
    have hB : (x2.1.val * g.NT + x2.2.val) % X.NT = x2.2.val := by rw [hm.NT, flat_mod _ _ x2.2.isLt]
    simp only [ExData.RxF]
    rw [if_pos hq, q_div hs2, q_mod hs2, hA, hB, hm.NC, sum_range_cells g, hm.w, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [hm.ns x x2, b2n_div, b2n_mod, hm.pt]
    unfold ExData.KR
    rw [hm.ab x x2, hm.t, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mem_range] at hs
    rw [ih x s hs]
    split_ifs <;> ring

theorem Clx_eq_Psid (hm : Match g D t X) (i : ℕ) : X.Clx i = Psid g hNR hNT D (i + 2) t := by
  rw [Psid_eq_Phi]
  unfold ExData.Clx
  congr 1
  rw [hm.NC, sum_range_cells g]
  apply Finset.sum_congr rfl
  intro x2 _
  have hA : (x2.1.val * g.NT + x2.2.val) / X.NT = x2.1.val := by rw [hm.NT, flat_div _ _ x2.2.isLt]
  have hB : (x2.1.val * g.NT + x2.2.val) % X.NT = x2.2.val := by rw [hm.NT, flat_mod _ _ x2.2.isLt]
  rw [hA, hB, sum_range_cells g, hm.w, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [hm.ns x x2, b2n_div, b2n_mod, hm.pt]
  unfold ExData.KR
  rw [hm.ab x x2, hm.t, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mem_range] at hs
  rw [RxF_eq_Phi hNR hNT hm i x s hs]
  ring

end Gen

/-! ## The run data as `DiscData` -/

/-- The real grid of a computational grid. -/
def gR (g : W2C.Grid) : GridR := ⟨g.N1, g.N2, g.NT⟩

/-- The table index of the cell pair `(ir, ir2)` at angular offset `d`. -/
def tidx (g : W2C.Grid) (ir ir2 : ℕ) (d : ℤ) : ℕ := (ir * g.NR + ir2) * g.ND + (d + ((g.NT - 1 : ℕ) : ℤ)).toNat

/-- The table data of a run, as real numbers. -/
noncomputable def discOf (g : W2C.Grid) (rings : Array Ring) (tab : Array (ℕ × ℤ)) (dtl : ℕ) : DiscData where
  w := fun ir => (rings[ir]!.areaLo.toNat : ℝ) / 2 ^ PR
  ub := fun ir => fx (ubInt rings[ir]!.euHi dtl)
  ab := fun ir ir2 d => fx tab[tidx g ir ir2 d]!.2
  sc := fun ir ir2 d => tab[tidx g ir ir2 d]!.1 == 1
  nf := fun ir => rings[ir]!.nflag

lemma idxOf_flat (g : W2C.Grid) (x x2 : Cell (gR g)) :
    idxOf g.NR g.NT g.ND x2.1.val x2.2.val (x.1.val * g.NT + x.2.val) = tidx g x.1.val x2.1.val (doff x x2) := by
  unfold idxOf tidx doff
  have h2 : x.2.val < g.NT := x.2.isLt
  rw [flat_div _ _ h2, flat_mod _ _ h2, toNat_off _ _ _ h2]

theorem match_run {g : W2C.Grid} {rings : Array Ring} {tab : Array (ℕ × ℤ)} (hr : rings.size = g.NR)
    (j dtl : ℕ) :
    Match (gR g) (discOf g rings tab dtl) ((j : ℝ) / 2 ^ dtl) (exOf g rings tab mkPassTab j dtl) where
  NT := rfl
  NC := rfl
  pt := rfl
  t := rfl
  w := fun _ => rfl
  ub := fun _ => rfl
  nb := by
    intro ir
    show (rings.map (fun R => if R.nflag then 1 else 0))[ir.val]! = b2n rings[ir.val]!.nflag
    rw [getElem!_map _ _ (by rw [hr]; exact ir.isLt)]
    rfl
  ab := by
    intro x x2
    show fx tab[idxOf g.NR g.NT g.ND x2.1.val x2.2.val (x.1.val * g.NT + x.2.val)]!.2 = _
    rw [idxOf_flat]
    rfl
  ns := by
    intro x x2
    have h2 : x2.2.val < g.NT := x2.2.isLt
    show (rings.map (fun R => if R.nflag then 1 else 0))[(x2.1.val * g.NT + x2.2.val) / g.NT]! * 2 +
        (if (tab.map (·.1 == 1))[idxOf g.NR g.NT g.ND ((x2.1.val * g.NT + x2.2.val) / g.NT)
          ((x2.1.val * g.NT + x2.2.val) % g.NT) (x.1.val * g.NT + x.2.val)]! then 1 else 0) = _
    rw [flat_div _ _ h2, flat_mod _ _ h2, idxOf_flat, getElem!_map _ _ (by rw [hr]; exact x2.1.isLt),
      getElem!_map' _ _ _ (by rfl)]
    rfl

/-- **Theorem A.** The exact closing sums of a production run are the discrete bound `Ψ^d` of its tables:
`Clx i = Ψ^d` with `i + 2` increments at `t = j 2^-dtl`. -/
theorem clx_eq_psid {g : W2C.Grid} {rings : Array Ring} {tab : Array (ℕ × ℤ)} (hr : rings.size = g.NR)
    (hNR : 0 < (gR g).NR) (hNT : 0 < (gR g).NT) (j dtl i : ℕ) :
    (exOf g rings tab mkPassTab j dtl).Clx i =
      Psid (gR g) hNR hNT (discOf g rings tab dtl) (i + 2) ((j : ℝ) / 2 ^ dtl) :=
  Clx_eq_Psid hNR hNT (match_run hr j dtl) i

end BHH.W2
