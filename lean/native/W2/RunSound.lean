/-
Soundness of one production run `W2C.runT4`: its outputs bound the exact closing sums `Clx` of the exact data of
the run (`exOf`).
-/
import W2.RecSound
import W2.KernSound

open Real

namespace BHH.W2

open W2C BHH.Cert BHH

/-- The rounded-up first-step exponent of a ring (a multiple of `2^dtl`). -/
def ubInt (e : ℤ) (dtl : ℕ) : ℤ := e + (2 ^ dtl - e % 2 ^ dtl) % 2 ^ dtl

/-- The exact data of the run `runT4 g rings tab e1 pt lower j dtl kmax`. -/
noncomputable def exOf (g : W2C.Grid) (rings : Array Ring) (tab : Array (ℕ × ℤ)) (pt : PassTab) (j dtl : ℕ) :
    ExData where
  NR := g.NR
  NT := g.NT
  ND := g.ND
  NC := g.NR * g.NT
  wR := fun ir => (rings[ir]!.areaLo.toNat : ℝ) / 2 ^ PR
  ubR := fun ir => fx (ubInt rings[ir]!.euHi dtl)
  abR := fun idx => fx tab[idx]!.2
  cls1 := tab.map (·.1 == 1)
  nb := rings.map (fun R => if R.nflag then 1 else 0)
  pt := pt
  t := (j : ℝ) / 2 ^ dtl

/-- The read-only data of the run (as in `runT4`). -/
def rdOf (g : W2C.Grid) (rings : Array Ring) (tab : Array (ℕ × ℤ)) (e1 : Array ℕ) (pt : PassTab) (lower : Bool)
    (j : ℕ) : RecData :=
  let kt : Array ℕ := e1.map fun x => kernFromE1 lower j x
  ⟨g.NR, g.NT, g.ND, g.NR * g.NT, kt.map (· >>> 31), kt.map (· &&& m31), tab.map (·.1 == 1),
    rings.map (·.areaLo.toNat), rings.map (fun R => if R.nflag then 1 else 0), pt⟩

lemma getElem!_map' {α β : Type*} [Inhabited α] [Inhabited β] (f : α → β) (a : Array α) (q : ℕ)
    (hdef : f default = default) : (a.map f)[q]! = f a[q]! := by
  by_cases hq : q < a.size
  · exact getElem!_map f a hq
  · rw [getElem!_neg (a.map f) q (by simpa using hq), getElem!_neg a q hq, hdef]

lemma compat_run (g : W2C.Grid) (hNT : 0 < g.NT) (rings : Array Ring) (tab : Array (ℕ × ℤ)) (e1 : Array ℕ)
    (pt : PassTab) (lower : Bool) (j dtl : ℕ) :
    Compat (rdOf g rings tab e1 pt lower j) (exOf g rings tab pt j dtl) where
  NR := rfl
  NT := rfl
  ND := rfl
  NC := rfl
  NCeq := rfl
  NTpos := hNT
  cls1 := rfl
  nb := rfl
  nb_le := by
    intro ir
    simp only [exOf]
    rw [getElem!_map' _ _ _ (by rfl)]
    split_ifs <;> omega
  pt := rfl
  w := by
    intro ir
    simp only [exOf, rdOf]
    rw [getElem!_map' _ _ _ (by rfl)]

lemma idxOf_lt {NR NT ND c2 c : ℕ} (hND : ND = 2 * NT - 1) (hNT : 0 < NT) (hc2 : c2 < NR * NT)
    (hc : c < NR * NT) : idxOf NR NT ND (c2 / NT) (c2 % NT) c < NR * NR * ND := by
  unfold idxOf
  have h1 : c2 / NT < NR := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hc2)
  have h2 : c / NT < NR := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hc)
  have h3 : c2 % NT < NT := Nat.mod_lt _ hNT
  have h4 : c % NT < NT := Nat.mod_lt _ hNT
  have h5 : c2 % NT + (NT - 1) - c % NT < ND := by omega
  have h6 : c / NT * NR + c2 / NT < NR * NR := by nlinarith
  calc (c / NT * NR + c2 / NT) * ND + (c2 % NT + (NT - 1) - c % NT)
      < (c / NT * NR + c2 / NT) * ND + ND := by omega
    _ = (c / NT * NR + c2 / NT + 1) * ND := by ring
    _ ≤ NR * NR * ND := Nat.mul_le_mul_right _ (by omega)

/-- Hypotheses on the inputs of a production run (all hold for `mkRunData`). -/
structure RunInputs (g : W2C.Grid) (rings : Array Ring) (tab : Array (ℕ × ℤ)) (e1lo e1hi : Array ℕ) (dtl : ℕ) :
    Prop where
  NTpos : 0 < g.NT
  ND : g.ND = 2 * g.NT - 1
  rings_size : rings.size = g.NR
  tab_size : tab.size = g.NR * g.NR * g.ND
  e1lo : e1lo = tab.map fun p => kern1 true dtl p.2
  e1hi : e1hi = tab.map fun p => kern1 false dtl p.2
  tab_dvd : ∀ idx < tab.size, (2 : ℤ) ^ dtl ∣ tab[idx]!.2
  tab_nonneg : ∀ idx < tab.size, 0 ≤ tab[idx]!.2

lemma ubInt_dvd (e : ℤ) (dtl : ℕ) : (2 : ℤ) ^ dtl ∣ ubInt e dtl := by
  unfold ubInt
  set q : ℤ := 2 ^ dtl with hqdef
  have hq : 0 < q := by positivity
  have hdm := Int.mul_ediv_add_emod e q
  have h0 : 0 ≤ e % q := Int.emod_nonneg _ hq.ne'
  have h1 : e % q < q := Int.emod_lt_of_pos _ hq
  rcases eq_or_lt_of_le h0 with hz | hpos
  · rw [← hz, sub_zero, Int.emod_self, add_zero]
    exact ⟨e / q, by linarith⟩
  · rw [Int.emod_eq_of_lt (by linarith) (by linarith)]
    exact ⟨e / q + 1, by linarith⟩

lemma exp_pow_eq (a : ℝ) (j dtl : ℕ) :
    Real.exp (-(a / 2 ^ dtl)) ^ j = Real.exp (-((j : ℝ) / 2 ^ dtl * a)) := by
  rw [← Real.exp_nat_mul]; congr 1; ring

/-- Kernel bounds of a run, lower direction. -/
lemma run_hK_lower {g : W2C.Grid} {rings : Array Ring} {tab : Array (ℕ × ℤ)} {e1lo e1hi : Array ℕ} {dtl : ℕ}
    (hin : RunInputs g rings tab e1lo e1hi dtl) (pt : PassTab) (j : ℕ) :
    let X := exOf g rings tab pt j dtl
    let rd := rdOf g rings tab e1lo pt true j
    ∀ c2 < X.NC, ∀ c < X.NC,
      ((rd.k1s[idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c]! * 2 ^ 31 +
        rd.k0s[idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c]! : ℕ) : ℝ) ≤
        2 ^ 62 * X.KR (idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c) := by
  intro X rd c2 hc2 c hc
  set idx := idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c with hidx
  have hidx_lt : idx < tab.size := by
    rw [hin.tab_size]; exact idxOf_lt hin.ND hin.NTpos hc2 hc
  have he1 : idx < e1lo.size := by rw [hin.e1lo]; simpa using hidx_lt
  have hkt : idx < (e1lo.map fun x => kernFromE1 true j x).size := by simpa using he1
  have e : rd.k1s[idx]! * 2 ^ 31 + rd.k0s[idx]! = kernFromE1 true j (kern1 true dtl tab[idx]!.2) := by
    simp only [rd, rdOf]
    rw [getElem!_map _ _ hkt, getElem!_map _ _ hkt, ← split31, getElem!_map _ _ he1, hin.e1lo,
      getElem!_map _ _ hidx_lt]
  rw [e]
  have h1 := kern1_lower dtl tab[idx]!.2 (hin.tab_dvd idx hidx_lt)
  have h2 := kernFromE1_lower j (kern1 true dtl tab[idx]!.2) h1
  rw [exp_pow_eq] at h2
  simpa [ExData.KR, X, exOf] using h2

/-- Kernel bounds of a run, upper direction. -/
lemma run_hK_upper {g : W2C.Grid} {rings : Array Ring} {tab : Array (ℕ × ℤ)} {e1lo e1hi : Array ℕ} {dtl : ℕ}
    (hin : RunInputs g rings tab e1lo e1hi dtl) (pt : PassTab) (j : ℕ) :
    let X := exOf g rings tab pt j dtl
    let rd := rdOf g rings tab e1hi pt false j
    ∀ c2 < X.NC, ∀ c < X.NC,
      2 ^ 62 * X.KR (idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c) ≤
      ((rd.k1s[idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c]! * 2 ^ 31 +
        rd.k0s[idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c]! : ℕ) : ℝ) ∧
      rd.k0s[idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c]! < 2 ^ 31 := by
  intro X rd c2 hc2 c hc
  set idx := idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c with hidx
  have hidx_lt : idx < tab.size := by
    rw [hin.tab_size]; exact idxOf_lt hin.ND hin.NTpos hc2 hc
  have he1 : idx < e1hi.size := by rw [hin.e1hi]; simpa using hidx_lt
  have hkt : idx < (e1hi.map fun x => kernFromE1 false j x).size := by simpa using he1
  have e : rd.k1s[idx]! * 2 ^ 31 + rd.k0s[idx]! = kernFromE1 false j (kern1 false dtl tab[idx]!.2) := by
    simp only [rd, rdOf]
    rw [getElem!_map _ _ hkt, getElem!_map _ _ hkt, ← split31, getElem!_map _ _ he1, hin.e1hi,
      getElem!_map _ _ hidx_lt]
  have hk0 : rd.k0s[idx]! < 2 ^ 31 := by
    simp only [rd, rdOf]; rw [getElem!_map _ _ hkt]; exact and_m31_lt _
  refine ⟨?_, hk0⟩
  rw [e]
  have h1 := kern1_upper dtl tab[idx]!.2 (hin.tab_dvd idx hidx_lt) (hin.tab_nonneg idx hidx_lt)
  have h2 := kernFromE1_upper j (kern1 false dtl tab[idx]!.2) (Real.exp_pos _).le h1
  rw [exp_pow_eq] at h2
  simpa [ExData.KR, X, exOf] using h2

/-- The first-step array of `runT4`. -/
def F0Of (g : W2C.Grid) (rings : Array Ring) (tab : Array (ℕ × ℤ)) (e1 : Array ℕ) (pt : PassTab) (lower : Bool)
    (j dtl : ℕ) : Array ℕ :=
  let rd := rdOf g rings tab e1 pt lower j
  let f1 : Array ℕ := rings.map fun R => kern lower j dtl (R.euHi + (2 ^ dtl - (R.euHi % 2 ^ dtl)) % 2 ^ dtl)
  Array.ofFn (n := rd.NC * 17) fun q =>
    let c := q.val / 17
    let D := q.val % 17
    let ir := c / rd.NT
    if pt.init1[rd.nb[ir]!]! == D then rd.w[ir]! * f1[ir]! else 0

lemma runT4_eq (g : W2C.Grid) (rings : Array Ring) (tab : Array (ℕ × ℤ)) (e1 : Array ℕ) (pt : PassTab)
    (lower : Bool) (j dtl kmax : ℕ) :
    runT4 g rings tab e1 pt lower j dtl kmax =
      recIter lower (rdOf g rings tab e1 pt lower j) (kmax - 2)
        (normF lower (F0Of g rings tab e1 pt lower j dtl)).1
        ((PR : ℤ) + 62 - ((normF lower (F0Of g rings tab e1 pt lower j dtl)).2 : ℤ)) [] := rfl

lemma F0_ir_lt {g : W2C.Grid} {rings : Array Ring} {tab : Array (ℕ × ℤ)} {e1lo e1hi : Array ℕ} {dtl : ℕ}
    (hin : RunInputs g rings tab e1lo e1hi dtl) {q : ℕ} (hq : q < g.NR * g.NT * 17) :
    q / 17 / g.NT < rings.size := by
  rw [hin.rings_size]
  exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact Nat.div_lt_of_lt_mul (by linarith))

lemma e2PR : (2 : ℝ) ^ (-((PR : ℤ) + 62)) = 1 / (2 ^ PR * 2 ^ 62) := by
  have : (2 : ℝ) ^ ((PR : ℤ) + 62) = 2 ^ PR * 2 ^ 62 := by
    rw [zpow_add₀ two_ne_zero, zpow_natCast]; norm_num
  rw [zpow_neg, this, one_div]

/-- The first step, lower direction. -/
lemma F0_lower {g : W2C.Grid} {rings : Array Ring} {tab : Array (ℕ × ℤ)} {e1lo e1hi : Array ℕ} {dtl : ℕ}
    (hin : RunInputs g rings tab e1lo e1hi dtl) (pt : PassTab) (j : ℕ) :
    ∀ q < (exOf g rings tab pt j dtl).NC * 17,
      ((F0Of g rings tab e1lo pt true j dtl)[q]! : ℝ) * (2 : ℝ) ^ (-((PR : ℤ) + 62)) ≤
        (exOf g rings tab pt j dtl).RxF 0 q := by
  intro q hq
  have hq' : q < g.NR * g.NT * 17 := hq
  have hir := F0_ir_lt hin hq'
  simp only [F0Of, rdOf]
  rw [getElem!_ofFn _ hq']
  simp only [ExData.RxF, exOf, hq', true_and]
  by_cases h : pt.init1[(rings.map fun R => if R.nflag then 1 else 0)[q / 17 / g.NT]!]! = q % 17
  · simp only [h, beq_self_eq_true, ite_true]
    rw [getElem!_map _ _ hir, getElem!_map _ _ hir]
    have hk := kern_lower j dtl (ubInt rings[q / 17 / g.NT]!.euHi dtl) (ubInt_dvd _ _)
    rw [e2PR]
    push_cast
    unfold ubInt at hk
    calc (rings[q / 17 / g.NT]!.areaLo.toNat : ℝ) *
          (kern true j dtl (rings[q / 17 / g.NT]!.euHi + (2 ^ dtl - rings[q / 17 / g.NT]!.euHi % 2 ^ dtl) % 2 ^ dtl) : ℝ) *
          (1 / (2 ^ PR * 2 ^ 62))
        = ((rings[q / 17 / g.NT]!.areaLo.toNat : ℝ) / 2 ^ PR) *
            ((kern true j dtl (rings[q / 17 / g.NT]!.euHi + (2 ^ dtl - rings[q / 17 / g.NT]!.euHi % 2 ^ dtl) % 2 ^ dtl) : ℝ) /
              2 ^ 62) := by ring
      _ ≤ ((rings[q / 17 / g.NT]!.areaLo.toNat : ℝ) / 2 ^ PR) *
            Real.exp (-((j : ℝ) / 2 ^ dtl * fx (rings[q / 17 / g.NT]!.euHi +
              (2 ^ dtl - rings[q / 17 / g.NT]!.euHi % 2 ^ dtl) % 2 ^ dtl))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_iff₀ (by positivity)]; linarith
      _ = _ := by unfold ubInt; ring_nf
  · have hb : ¬ (pt.init1[(rings.map fun R => if R.nflag then 1 else 0)[q / 17 / g.NT]!]! == q % 17) = true := by
      simpa using h
    simp [hb, h]

/-- The first step, upper direction. -/
lemma F0_upper {g : W2C.Grid} {rings : Array Ring} {tab : Array (ℕ × ℤ)} {e1lo e1hi : Array ℕ} {dtl : ℕ}
    (hin : RunInputs g rings tab e1lo e1hi dtl) (pt : PassTab) (j : ℕ)
    (hub : ∀ ir : ℕ, 0 ≤ ubInt rings[ir]!.euHi dtl) :
    ∀ q < (exOf g rings tab pt j dtl).NC * 17,
      (exOf g rings tab pt j dtl).RxF 0 q ≤
        ((F0Of g rings tab e1hi pt false j dtl)[q]! : ℝ) * (2 : ℝ) ^ (-((PR : ℤ) + 62)) := by
  intro q hq
  have hq' : q < g.NR * g.NT * 17 := hq
  have hir := F0_ir_lt hin hq'
  simp only [F0Of, rdOf]
  rw [getElem!_ofFn _ hq']
  simp only [ExData.RxF, exOf, hq', true_and]
  by_cases h : pt.init1[(rings.map fun R => if R.nflag then 1 else 0)[q / 17 / g.NT]!]! = q % 17
  · simp only [h, beq_self_eq_true, ite_true]
    rw [getElem!_map _ _ hir, getElem!_map _ _ hir]
    have hk := kern_upper j dtl (ubInt rings[q / 17 / g.NT]!.euHi dtl) (ubInt_dvd _ _) (hub _)
    rw [e2PR]
    push_cast
    unfold ubInt at hk
    calc ((rings[q / 17 / g.NT]!.areaLo.toNat : ℝ) / 2 ^ PR) *
            Real.exp (-((j : ℝ) / 2 ^ dtl * fx (ubInt rings[q / 17 / g.NT]!.euHi dtl)))
        = ((rings[q / 17 / g.NT]!.areaLo.toNat : ℝ) / 2 ^ PR) *
            Real.exp (-((j : ℝ) / 2 ^ dtl * fx (rings[q / 17 / g.NT]!.euHi +
              (2 ^ dtl - rings[q / 17 / g.NT]!.euHi % 2 ^ dtl) % 2 ^ dtl))) := by unfold ubInt; ring_nf
      _ ≤ ((rings[q / 17 / g.NT]!.areaLo.toNat : ℝ) / 2 ^ PR) *
            ((kern false j dtl (rings[q / 17 / g.NT]!.euHi + (2 ^ dtl - rings[q / 17 / g.NT]!.euHi % 2 ^ dtl) % 2 ^ dtl) : ℝ) /
              2 ^ 62) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [le_div_iff₀ (by positivity)]; linarith
      _ = _ := by ring
  · have hb : ¬ (pt.init1[(rings.map fun R => if R.nflag then 1 else 0)[q / 17 / g.NT]!]! == q % 17) = true := by
      simpa using h
    simp [hb, h]

lemma F0Of_size (g : W2C.Grid) (rings : Array Ring) (tab : Array (ℕ × ℤ)) (e1 : Array ℕ) (pt : PassTab)
    (lower : Bool) (j dtl : ℕ) : (F0Of g rings tab e1 pt lower j dtl).size = g.NR * g.NT * 17 := by
  simp [F0Of, rdOf]

/-- A production run, lower direction: entry `m` of `runT4 ... true` is a lower bound of `Clx m`. -/
theorem runT4_lower {g : W2C.Grid} {rings : Array Ring} {tab : Array (ℕ × ℤ)} {e1lo e1hi : Array ℕ} {dtl : ℕ}
    (hin : RunInputs g rings tab e1lo e1hi dtl) (pt : PassTab) (j kmax : ℕ) :
    ∀ m < kmax - 2,
      ((runT4 g rings tab e1lo pt true j dtl kmax)[m]!.1 : ℝ) *
        (2 : ℝ) ^ (-(runT4 g rings tab e1lo pt true j dtl kmax)[m]!.2) ≤ (exOf g rings tab pt j dtl).Clx m := by
  intro m hm
  rw [runT4_eq]
  have hc := compat_run g hin.NTpos rings tab e1lo pt true j dtl
  have hK := run_hK_lower hin pt j
  have hF1 : ∀ q < (exOf g rings tab pt j dtl).NC * 17,
      ((normF true (F0Of g rings tab e1lo pt true j dtl)).1[q]! : ℝ) *
        (2 : ℝ) ^ (-((PR : ℤ) + 62 - ((normF true (F0Of g rings tab e1lo pt true j dtl)).2 : ℤ))) ≤
        (exOf g rings tab pt j dtl).RxF 0 q := by
    intro q hq
    have hqs : q < (F0Of g rings tab e1lo pt true j dtl).size := by rw [F0Of_size]; exact hq
    exact le_trans (normF_lower hqs) (F0_lower hin pt j q hq)
  have H := recIter_lower _ _ hc hK (kmax - 2) 0 _ _ [] hF1
  have := H.2.2 m hm
  simpa using this

/-- A production run, upper direction. -/
theorem runT4_upper {g : W2C.Grid} {rings : Array Ring} {tab : Array (ℕ × ℤ)} {e1lo e1hi : Array ℕ} {dtl : ℕ}
    (hin : RunInputs g rings tab e1lo e1hi dtl) (hub : ∀ ir : ℕ, 0 ≤ ubInt rings[ir]!.euHi dtl)
    (pt : PassTab) (j kmax : ℕ) :
    ∀ m < kmax - 2, (exOf g rings tab pt j dtl).Clx m ≤
      ((runT4 g rings tab e1hi pt false j dtl kmax)[m]!.1 : ℝ) *
        (2 : ℝ) ^ (-(runT4 g rings tab e1hi pt false j dtl kmax)[m]!.2) := by
  intro m hm
  rw [runT4_eq]
  have hc := compat_run g hin.NTpos rings tab e1hi pt false j dtl
  have hK := run_hK_upper hin pt j
  have hF1 : ∀ q < (exOf g rings tab pt j dtl).NC * 17,
      (exOf g rings tab pt j dtl).RxF 0 q ≤
      ((normF false (F0Of g rings tab e1hi pt false j dtl)).1[q]! : ℝ) *
        (2 : ℝ) ^ (-((PR : ℤ) + 62 - ((normF false (F0Of g rings tab e1hi pt false j dtl)).2 : ℤ))) := by
    intro q hq
    have hqs : q < (F0Of g rings tab e1hi pt false j dtl).size := by rw [F0Of_size]; exact hq
    exact le_trans (F0_upper hin pt j hub q hq) (normF_upper hqs)
  have H := recIter_upper _ _ hc hK (kmax - 2) 0 _ _ [] hF1
  have := H.2.2 m hm
  simpa using this

end BHH.W2
