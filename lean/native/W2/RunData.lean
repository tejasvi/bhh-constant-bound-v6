/-
The shared data of a production run (`W2C.mkRunData`, with or without tasks): the explicit table entries
(`tab[(ir * NR + ir2) * ND + di]` is the entry of `(ir, ir2, d)`), the kernel arrays `e1`, and the hypotheses
`RunInputs` of the recursion soundness.  Also the meaning of `shardOK = true` and of the claim checks.
-/
import W2.Unroll
import W2Cert.Shard

open Real

namespace BHH.W2

open W2C BHH.Cert BHH

/-! ## Array lemmas -/

lemma task_get_spawn {α : Type*} (f : Unit → α) (p : Task.Priority) : (Task.spawn f p).get = f () := rfl

lemma array_range_add (a b : ℕ) {β : Type*} (f : ℕ → β) :
    (Array.range (a + b)).map f = (Array.range a).map f ++ (Array.range b).map (fun i => f (a + i)) := by
  apply Array.toList_inj.mp
  simp only [Array.toList_map, Array.toList_range, Array.toList_append, List.range_add, List.map_append,
    List.map_map]
  rfl

/-- Concatenating rows `(Array.range L).map (G ir)` for `ir < n`. -/
lemma foldl_rows {β : Type*} (L : ℕ) (G : ℕ → ℕ → β) :
    ∀ n, ((List.range n).map fun ir => (Array.range L).map (G ir)).foldl (· ++ ·) #[] =
      (Array.range (n * L)).map (fun idx => G (idx / L) (idx % L))
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.foldl_append, foldl_rows L G n, List.map_singleton,
      List.foldl_cons, List.foldl_nil, Nat.succ_mul, array_range_add]
    congr 1
    apply Array.toList_inj.mp
    simp only [Array.toList_map, Array.toList_range]
    apply List.map_congr_left
    intro q hq
    rw [List.mem_range] at hq
    rw [flat_div _ _ hq, flat_mod _ _ hq]

/-- Concatenating `P` chunks of length `chunk` of `(Array.range n).map f`. -/
lemma foldl_chunks {β : Type*} (n chunk : ℕ) (f : ℕ → β) :
    ∀ P, ((List.range P).map fun p => Task.spawn fun _ =>
        (Array.range (Min.min chunk (n - Min.min n (p * chunk)))).map fun i => f (p * chunk + i)).foldl
        (fun acc t => acc ++ t.get) #[] =
      (Array.range (Min.min n (P * chunk))).map f
  | 0 => by simp
  | P + 1 => by
    rw [List.range_succ, List.map_append, List.foldl_append, foldl_chunks n chunk f P, List.map_singleton,
      List.foldl_cons, List.foldl_nil, task_get_spawn]
    by_cases h : n ≤ P * chunk
    · have e1 : Min.min n (P * chunk) = n := min_eq_left h
      have e2 : Min.min n ((P + 1) * chunk) = n := min_eq_left (by nlinarith)
      rw [e1, e2, Nat.sub_self, Nat.min_zero]
      simp
    · push_neg at h
      have e1 : Min.min n (P * chunk) = P * chunk := min_eq_right h.le
      have e2 : Min.min n ((P + 1) * chunk) = P * chunk + Min.min chunk (n - P * chunk) := by
        rw [Nat.succ_mul]; omega
      rw [e1, e2, array_range_add]

lemma map_range_getElem! {α β : Type*} [Inhabited α] (a : Array α) (g : α → β) :
    (Array.range a.size).map (fun i => g a[i]!) = a.map g := by
  apply Array.ext
  · simp
  · intro i h1 h2
    simp only [Array.getElem_map, Array.getElem_range]
    rw [getElem!_pos a i (by simpa using h1)]

lemma range_getElem! {n idx : ℕ} (h : idx < n) : (Array.range n)[idx]! = idx := by
  rw [getElem!_pos (Array.range n) idx (by simpa using h)]
  simp

/-! ## The run data -/

/-- The raw table, explicitly. -/
lemma rawTab_eq (g : Grid) (rings : Array Ring) (par : Bool) :
    rawTab g rings par = (Array.range (g.NR * (g.NR * g.ND))).map fun idx =>
      entryF g.prune rings (mkAData g) (mkDTab g)[idx % (g.NR * g.ND) % g.ND]! (idx / (g.NR * g.ND))
        (idx % (g.NR * g.ND) / g.ND) := by
  have hrows : (if par then ((List.range g.NR).map fun ir => Task.spawn fun _ =>
        (Array.range (g.NR * g.ND)).map fun q => entryF g.prune rings (mkAData g) (mkDTab g)[q % g.ND]! ir (q / g.ND)).map
        Task.get
      else (List.range g.NR).map fun ir =>
        (Array.range (g.NR * g.ND)).map fun q => entryF g.prune rings (mkAData g) (mkDTab g)[q % g.ND]! ir (q / g.ND)) =
      (List.range g.NR).map fun ir =>
        (Array.range (g.NR * g.ND)).map fun q => entryF g.prune rings (mkAData g) (mkDTab g)[q % g.ND]! ir (q / g.ND) := by
    split_ifs
    · rw [List.map_map]; rfl
    · rfl
  unfold rawTab
  simp only
  rw [hrows, foldl_rows (g.NR * g.ND) (fun ir q => entryF g.prune rings (mkAData g) (mkDTab g)[q % g.ND]! ir (q / g.ND))]

/-- The kernel array of the run data, in both modes. -/
lemma e1_eq (lower : Bool) (dtl : ℕ) (tab : Array (ℕ × ℤ)) (par : Bool) :
    (if par then
      ((List.range 64).map fun p => Task.spawn fun _ =>
        (Array.range (Min.min ((tab.size + 63) / 64) (tab.size - Min.min tab.size (p * ((tab.size + 63) / 64))))).map
          fun i => kern1 lower dtl tab[p * ((tab.size + 63) / 64) + i]!.2).foldl (fun acc t => acc ++ t.get) #[]
    else tab.map fun x => kern1 lower dtl x.2) = tab.map fun x => kern1 lower dtl x.2 := by
  split_ifs
  · rw [foldl_chunks tab.size ((tab.size + 63) / 64) (fun i => kern1 lower dtl tab[i]!.2) 64]
    rw [min_eq_left (by omega), map_range_getElem! tab (fun x => kern1 lower dtl x.2)]
  · rfl

lemma mkRunData_rings (g : Grid) (dtl : ℕ) (par : Bool) :
    (mkRunData g dtl par).rings = (Array.range g.NR).map (mkRing g) := rfl

lemma mkRunData_tab (g : Grid) (dtl : ℕ) (par : Bool) :
    (mkRunData g dtl par).tab = prepTab dtl (rawTab g ((Array.range g.NR).map (mkRing g)) par) := rfl

lemma mkRunData_e1lo (g : Grid) (dtl : ℕ) (par : Bool) :
    (mkRunData g dtl par).e1lo = (mkRunData g dtl par).tab.map fun x => kern1 true dtl x.2 := by
  rw [← e1_eq true dtl _ par]
  rfl

lemma mkRunData_e1hi (g : Grid) (dtl : ℕ) (par : Bool) :
    (mkRunData g dtl par).e1hi = (mkRunData g dtl par).tab.map fun x => kern1 false dtl x.2 := by
  rw [← e1_eq false dtl _ par]
  rfl

lemma mkRunData_pt (g : Grid) (dtl : ℕ) (par : Bool) : (mkRunData g dtl par).pt = mkPassTab := rfl

lemma tab_size (g : Grid) (dtl : ℕ) (par : Bool) :
    (mkRunData g dtl par).tab.size = g.NR * g.NR * g.ND := by
  rw [mkRunData_tab, prepTab, Array.size_map, rawTab_eq, Array.size_map, Array.size_range, Nat.mul_assoc]

/-- The prepared entry: `ā` clamped at `0` and rounded up to a multiple of `2^dtl`. -/
def prepE (dtl : ℕ) (p : ℕ × ℤ) : ℕ × ℤ := (p.1, ubInt (Max.max p.2 0) dtl)

lemma prepTab_eq (dtl : ℕ) (raw : Array (ℕ × ℤ)) : prepTab dtl raw = raw.map (prepE dtl) := by
  unfold prepTab prepE ubInt
  rfl

/-- The table entry of index `idx`. -/
lemma tab_getElem (g : Grid) (dtl : ℕ) (par : Bool) {idx : ℕ} (hidx : idx < g.NR * g.NR * g.ND) :
    (mkRunData g dtl par).tab[idx]! = prepE dtl (entryF g.prune ((Array.range g.NR).map (mkRing g)) (mkAData g)
      (mkDTab g)[idx % (g.NR * g.ND) % g.ND]! (idx / (g.NR * g.ND)) (idx % (g.NR * g.ND) / g.ND)) := by
  have hidx' : idx < g.NR * (g.NR * g.ND) := by rw [← Nat.mul_assoc]; exact hidx
  rw [mkRunData_tab, prepTab_eq, rawTab_eq, getElem!_map _ _ (by simpa using hidx'),
    getElem!_map _ _ (by simpa using hidx'), range_getElem! hidx']

lemma ubInt_nonneg {e : ℤ} (he : 0 ≤ e) (dtl : ℕ) : 0 ≤ ubInt e dtl := by
  unfold ubInt
  have : 0 ≤ (2 ^ dtl - e % 2 ^ dtl) % 2 ^ dtl := Int.emod_nonneg _ (by positivity)
  linarith

lemma le_ubInt (e : ℤ) (dtl : ℕ) : e ≤ ubInt e dtl := by
  unfold ubInt
  have : 0 ≤ (2 ^ dtl - e % 2 ^ dtl) % 2 ^ dtl := Int.emod_nonneg _ (by positivity)
  linarith

/-- The hypotheses of the recursion soundness hold for the run data. -/
theorem runInputs_mk (g : Grid) (hNT : 0 < g.NT) (dtl : ℕ) (par : Bool) :
    RunInputs g (mkRunData g dtl par).rings (mkRunData g dtl par).tab (mkRunData g dtl par).e1lo
      (mkRunData g dtl par).e1hi dtl where
  NTpos := hNT
  ND := rfl
  rings_size := by rw [mkRunData_rings, Array.size_map, Array.size_range]
  tab_size := tab_size g dtl par
  e1lo := mkRunData_e1lo g dtl par
  e1hi := mkRunData_e1hi g dtl par
  tab_dvd := by
    intro idx hidx
    rw [tab_size] at hidx
    rw [tab_getElem g dtl par hidx]
    exact ubInt_dvd _ _
  tab_nonneg := by
    intro idx hidx
    rw [tab_size] at hidx
    rw [tab_getElem g dtl par hidx]
    exact ubInt_nonneg (le_max_right _ _) _

end BHH.W2
