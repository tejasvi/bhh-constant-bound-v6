/-
Soundness of the production recursion `W2C.recStep` / `W2C.recIter`: the stored integers, read at their scale
`2^-E`, bound the exact real recursion `RxF` from below (`lower = true`) or above.
-/
import W2.RecLoop
import BHH.Interfaces

open Real

namespace BHH.W2

open W2C BHH.Cert

/-- The exact recursion (flat index `q = c * 17 + s`, `c < NC` a cell, `s < 17` a state index), for the read-only
data of a run: ring weights `wR`, first-step exponents `ubR`, pair exponents `abR` (by table index), kernels
`e^{-t abR}`. -/
structure ExData where
  NR : ℕ
  NT : ℕ
  ND : ℕ
  NC : ℕ
  wR : ℕ → ℝ
  ubR : ℕ → ℝ
  abR : ℕ → ℝ
  cls1 : Array Bool
  nb : Array ℕ
  pt : PassTab
  t : ℝ

namespace ExData

variable (X : ExData)

/-- kernel of the table entry `idx` -/
noncomputable def KR (idx : ℕ) : ℝ := Real.exp (-(X.t * X.abR idx))

/-- the pre-merge row `ns` of the target `c2` and source `c` -/
def nsOf (c2 c : ℕ) : ℕ :=
  X.nb[c2 / X.NT]! * 2 + (if X.cls1[idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c]! then 1 else 0)

/-- The exact recursion: `RxF i q` after `i + 1` increments. -/
noncomputable def RxF : ℕ → ℕ → ℝ
  | 0, q =>
    if q < X.NC * 17 ∧ X.pt.init1[X.nb[q / 17 / X.NT]!]! = q % 17 then
      X.wR (q / 17 / X.NT) * Real.exp (-(X.t * X.ubR (q / 17 / X.NT))) else 0
  | i + 1, q2 =>
    if q2 < X.NC * 17 then
      X.wR (q2 / 17 / X.NT) * ∑ c ∈ Finset.range X.NC,
        X.KR (idxOf X.NR X.NT X.ND (q2 / 17 / X.NT) (q2 / 17 % X.NT) c) *
          ∑ D ∈ Finset.range 17,
            if X.pt.trans[(D * 2 + X.nsOf (q2 / 17) c / 2) * 2 + X.nsOf (q2 / 17) c % 2]! = q2 % 17
            then RxF i (c * 17 + D) else 0
    else 0

/-- The exact closing sum after `i + 1` increments (`Ψ` for `i + 2` increments). -/
noncomputable def Clx (i : ℕ) : ℝ :=
  (1 / 2) * ∑ c2 ∈ Finset.range X.NC, X.wR (c2 / X.NT) * ∑ c ∈ Finset.range X.NC,
    X.KR (idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c) *
      ∑ D ∈ Finset.range 17,
        (X.pt.close2[(D * 2 + X.nsOf c2 c / 2) * 2 + X.nsOf c2 c % 2]! : ℝ) * X.RxF i (c * 17 + D)

lemma KR_pos (idx : ℕ) : 0 < X.KR idx := Real.exp_pos _

lemma RxF_nonneg (hw : ∀ ir, 0 ≤ X.wR ir) : ∀ i q, 0 ≤ X.RxF i q
  | 0, q => by
    simp only [RxF]; split_ifs
    · exact mul_nonneg (hw _) (Real.exp_pos _).le
    · exact le_rfl
  | i + 1, q => by
    simp only [RxF]; split_ifs
    · apply mul_nonneg (hw _)
      apply Finset.sum_nonneg; intro c _
      apply mul_nonneg (X.KR_pos _).le
      apply Finset.sum_nonneg; intro D _
      split_ifs
      · exact RxF_nonneg hw i _
      · exact le_rfl
    · exact le_rfl

end ExData

/-! ## Index arithmetic and array access -/

lemma decode_q (ns c D2 NC : ℕ) (hc : c < NC) (hD : D2 < 17) :
    ((ns * NC + c) * 17 + D2) / (NC * 17) = ns ∧ ((ns * NC + c) * 17 + D2) / 17 % NC = c ∧
      ((ns * NC + c) * 17 + D2) % 17 = D2 := by
  have h17 : ((ns * NC + c) * 17 + D2) / 17 = ns * NC + c := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num : 0 < 17), Nat.div_eq_of_lt hD, zero_add]
  refine ⟨?_, ?_, ?_⟩
  · apply Nat.div_eq_of_lt_le
    · nlinarith
    · nlinarith
  · rw [h17, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hD]

lemma decode_o (ns c NC : ℕ) (hc : c < NC) : (ns * NC + c) / NC = ns ∧ (ns * NC + c) % NC = c := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < NC), Nat.div_eq_of_lt hc, zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

lemma getElem!_ofFn {α : Type*} [Inhabited α] {n : ℕ} (f : Fin n → α) {q : ℕ} (hq : q < n) :
    (Array.ofFn f)[q]! = f ⟨q, hq⟩ := by
  rw [getElem!_pos (Array.ofFn f) q (by simpa using hq)]
  simp

lemma getElem!_map {α β : Type*} [Inhabited α] [Inhabited β] (f : α → β) (a : Array α) {q : ℕ}
    (hq : q < a.size) : (a.map f)[q]! = f a[q]! := by
  rw [getElem!_pos (a.map f) q (by simpa using hq), getElem!_pos a q hq]
  simp

lemma count_filter_range (p : ℕ → Bool) {D2 : ℕ} (hD : D2 < 17) :
    ((List.range 17).filter p).count D2 = if p D2 then 1 else 0 := by
  by_cases h : p D2 = true
  · rw [List.count_filter h, if_pos h]
    exact List.count_eq_one_of_mem List.nodup_range (List.mem_range.mpr hD)
  · rw [if_neg h, List.count_eq_zero]
    intro hm
    rw [List.mem_filter] at hm
    exact h hm.2

/-! ## The components of `recStep` -/

section Comp
variable (lower : Bool) (rd : RecData) (F : Array ℕ)

def GOf : Array ℕ := Array.ofFn (n := 4 * rd.NC * 17) fun q =>
  gEntry rd.pt F (q.val / (rd.NC * 17)) ((q.val / 17) % rd.NC) (q.val % 17)
def VOf : Array ℕ := Array.ofFn (n := 4 * rd.NC) fun q => vEntry rd.pt F (q.val / rd.NC) (q.val % rd.NC)
def nzOf : Array (List ℕ) := Array.ofFn (n := 4 * rd.NC) fun q =>
  (List.range 17).filter fun D2 => (GOf rd F)[q.val * 17 + D2]! != 0
def accOf (c2 : ℕ) : Array ℕ × ℕ :=
  srcLoopF lower rd.NR rd.NT rd.ND rd.NC rd.nb[c2 / rd.NT]! (c2 / rd.NT) (c2 % rd.NT) rd.k1s rd.k0s rd.cls1
    ((GOf rd F).map (· >>> 31)) ((GOf rd F).map (· &&& m31)) ((VOf rd F).map (· >>> 31))
    ((VOf rd F).map (· &&& m31)) (nzOf rd F) rd.NC (Array.replicate 17 0) 0
def tgtOf (c2 : ℕ) : Array ℕ × ℕ :=
  ((accOf lower rd F c2).1.map (rd.w[c2 / rd.NT]! * ·), rd.w[c2 / rd.NT]! * (accOf lower rd F c2).2)
def rowsOf : Array (Array ℕ × ℕ) := Array.ofFn (n := rd.NC) fun c2 => tgtOf lower rd F c2.val

lemma recStep_eq : recStep lower rd F =
    (Array.ofFn (n := rd.NC * 17) fun q => (rowsOf lower rd F)[q.val / 17]!.1[q.val % 17]!,
     (List.range rd.NC).foldl (fun acc c2 => acc + (rowsOf lower rd F)[c2]!.2) 0) := rfl

lemma GOf_get {ns c D2 : ℕ} (hns : ns < 4) (hc : c < rd.NC) (hD : D2 < 17) :
    (GOf rd F)[(ns * rd.NC + c) * 17 + D2]! = gEntry rd.pt F ns c D2 := by
  have hq : (ns * rd.NC + c) * 17 + D2 < 4 * rd.NC * 17 := by nlinarith
  unfold GOf
  rw [getElem!_ofFn _ hq]
  obtain ⟨h1, h2, h3⟩ := decode_q ns c D2 rd.NC hc hD
  simp only [h1, h2, h3]

lemma GOf_size : (GOf rd F).size = 4 * rd.NC * 17 := by simp [GOf]

lemma VOf_get {ns c : ℕ} (hns : ns < 4) (hc : c < rd.NC) :
    (VOf rd F)[ns * rd.NC + c]! = vEntry rd.pt F ns c := by
  have hq : ns * rd.NC + c < 4 * rd.NC := by nlinarith
  unfold VOf
  rw [getElem!_ofFn _ hq]
  obtain ⟨h1, h2⟩ := decode_o ns c rd.NC hc
  simp only [h1, h2]

lemma VOf_size : (VOf rd F).size = 4 * rd.NC := by simp [VOf]

lemma nzOf_count {ns c D2 : ℕ} (hns : ns < 4) (hc : c < rd.NC) (hD : D2 < 17) :
    ((nzOf rd F)[ns * rd.NC + c]!).count D2 =
      if gEntry rd.pt F ns c D2 ≠ 0 then 1 else 0 := by
  have hq : ns * rd.NC + c < 4 * rd.NC := by nlinarith
  unfold nzOf
  rw [getElem!_ofFn _ hq]
  simp only
  rw [count_filter_range _ hD, GOf_get rd F hns hc hD]
  by_cases h : gEntry rd.pt F ns c D2 = 0 <;> simp [h]

lemma nzOf_lt (o : ℕ) : ∀ d ∈ (nzOf rd F)[o]!, d < 17 := by
  intro d hd
  by_cases ho : o < 4 * rd.NC
  · unfold nzOf at hd
    rw [getElem!_ofFn _ ho] at hd
    simp only [List.mem_filter, List.mem_range] at hd
    exact hd.1
  · rw [getElem!_neg _ _ (by simpa [nzOf] using ho)] at hd
    change d ∈ ([] : List ℕ) at hd
    simp at hd

lemma GOf_get' {N ns c D2 : ℕ} (hN : rd.NC = N) (hns : ns < 4) (hc : c < N) (hD : D2 < 17) :
    (GOf rd F)[(ns * N + c) * 17 + D2]! = gEntry rd.pt F ns c D2 := by
  subst hN; exact GOf_get rd F hns hc hD

lemma VOf_get' {N ns c : ℕ} (hN : rd.NC = N) (hns : ns < 4) (hc : c < N) :
    (VOf rd F)[ns * N + c]! = vEntry rd.pt F ns c := by
  subst hN; exact VOf_get rd F hns hc

lemma nzOf_count' {N ns c D2 : ℕ} (hN : rd.NC = N) (hns : ns < 4) (hc : c < N) (hD : D2 < 17) :
    ((nzOf rd F)[ns * N + c]!).count D2 = if gEntry rd.pt F ns c D2 ≠ 0 then 1 else 0 := by
  subst hN; exact nzOf_count rd F hns hc hD

end Comp

/-! ## One step, lower direction -/

/-- The read-only data `rd` of a run and the exact data `X` describe the same run. -/
structure Compat (rd : RecData) (X : ExData) : Prop where
  NR : rd.NR = X.NR
  NT : rd.NT = X.NT
  ND : rd.ND = X.ND
  NC : rd.NC = X.NC
  NCeq : X.NC = X.NR * X.NT
  NTpos : 0 < X.NT
  cls1 : rd.cls1 = X.cls1
  nb : rd.nb = X.nb
  nb_le : ∀ ir : ℕ, X.nb[ir]! ≤ 1
  pt : rd.pt = X.pt
  w : ∀ ir : ℕ, X.wR ir = (rd.w[ir]! : ℝ) / 2 ^ PR

lemma zp2 (a b : ℤ) : (2 : ℝ) ^ (a + b) = 2 ^ a * 2 ^ b := zpow_add₀ two_ne_zero a b

/-- One product, lower direction: `[g ≠ 0] mulTop true (g >>> 31) (g &&& m31) k1 k0 ≤ g K / 2^76`. -/
lemma term_lower (g k1 k0 : ℕ) :
    ((if g ≠ 0 then 1 else 0 : ℕ) * mulTop true (g >>> 31) (g &&& m31) k1 k0 : ℝ) ≤
      (g : ℝ) * ((k1 * 2 ^ 31 + k0 : ℕ) : ℝ) / 2 ^ 76 := by
  by_cases hg : g = 0
  · simp [hg]
  · simp only [hg, ne_eq, not_false_eq_true, ite_true, Nat.cast_one, one_mul]
    have := mulTop_lower_le (g >>> 31) (g &&& m31) k1 k0
    rw [← split31 g] at this
    push_cast at this ⊢
    linarith

/-- The closing product, lower direction. -/
lemma vterm_lower (v k1 k0 : ℕ) :
    (mulTop true (v >>> 31) (v &&& m31) k1 k0 : ℝ) ≤ (v : ℝ) * ((k1 * 2 ^ 31 + k0 : ℕ) : ℝ) / 2 ^ 76 := by
  have := mulTop_lower_le (v >>> 31) (v &&& m31) k1 k0
  rw [← split31 v] at this
  push_cast at this ⊢
  linarith

/-- The source sum of one target entry, lower direction. -/
lemma acc_lower (rd : RecData) (X : ExData) (hc : Compat rd X)
    (hK : ∀ c2 < X.NC, ∀ c < X.NC,
      ((rd.k1s[idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c]! * 2 ^ 31 +
        rd.k0s[idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c]! : ℕ) : ℝ) ≤
        2 ^ 62 * X.KR (idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c))
    (F : Array ℕ) (E : ℤ) (i : ℕ) (hF : ∀ q < X.NC * 17, (F[q]! : ℝ) * (2 : ℝ) ^ (-E) ≤ X.RxF i q)
    {c2 D2 : ℕ} (hc2 : c2 < X.NC) (hD2 : D2 < 17) :
    ((accOf true rd F c2).1[D2]! : ℝ) * (2 : ℝ) ^ (-(E - 14)) ≤
      ∑ c ∈ Finset.range X.NC, X.KR (idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c) *
        ∑ D ∈ Finset.range 17,
          if X.pt.trans[(D * 2 + X.nsOf c2 c / 2) * 2 + X.nsOf c2 c % 2]! = D2
          then X.RxF i (c * 17 + D) else 0 := by
  obtain ⟨hNR, hNT, hND, hNC, _, _, hcls, hnb, hnbl, hpt, _⟩ := hc
  have hspec := srcLoopF_spec true rd.NR rd.NT rd.ND rd.NC rd.nb[c2 / rd.NT]! (c2 / rd.NT) (c2 % rd.NT)
    rd.k1s rd.k0s rd.cls1 ((GOf rd F).map (· >>> 31)) ((GOf rd F).map (· &&& m31)) ((VOf rd F).map (· >>> 31))
    ((VOf rd F).map (· &&& m31)) (nzOf rd F) rd.NC (Array.replicate 17 0) 0
    (by intro o d hd; simpa using nzOf_lt rd F o d hd)
  unfold accOf
  rw [hspec.2.1 D2]
  have hrep : (Array.replicate 17 0 : Array ℕ)[D2]! = 0 := by
    rw [getElem!_pos _ D2 (by simpa using hD2)]; simp
  rw [hrep, zero_add]
  rw [Nat.cast_sum, Finset.sum_mul]
  rw [hNR, hNT, hND, hNC]
  apply Finset.sum_le_sum
  intro c hcm
  rw [Finset.mem_range] at hcm
  -- the row `ns` and the indices
  set idx := idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c with hidx
  set ns := X.nsOf c2 c with hns
  have hns4 : ns < 4 := by
    have := hnbl (c2 / X.NT)
    simp only [hns, ExData.nsOf]; split_ifs <;> omega
  have ho : oOf X.NR X.NT X.ND X.NC rd.nb[c2 / X.NT]! (c2 / X.NT) (c2 % X.NT) rd.cls1 c = ns * X.NC + c := by
    simp only [oOf, hns, ExData.nsOf, hnb, hcls, idx]
  rw [ho]
  have hq : (ns * X.NC + c) * 17 + D2 < (GOf rd F).size := by rw [GOf_size, hNC]; nlinarith
  rw [getElem!_map _ _ hq, getElem!_map _ _ hq]
  rw [nzOf_count' rd F hNC hns4 hcm hD2, GOf_get' rd F hNC hns4 hcm hD2]
  set g := gEntry rd.pt F ns c D2 with hg
  have ht := term_lower g rd.k1s[idx]! rd.k0s[idx]!
  have hKc := hK c2 hc2 c hcm
  rw [← hidx] at hKc
  -- the exact pre-merge sum bounds g
  have hgE : (g : ℝ) * (2 : ℝ) ^ (-E) ≤ ∑ D ∈ Finset.range 17,
      if X.pt.trans[(D * 2 + ns / 2) * 2 + ns % 2]! = D2 then X.RxF i (c * 17 + D) else 0 := by
    rw [hg, gEntry_eq, Nat.cast_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro D hD
    rw [Finset.mem_range] at hD
    rw [hpt]
    split_ifs
    · exact hF _ (by nlinarith)
    · simp
  have hg0 : (0 : ℝ) ≤ (g : ℝ) * (2 : ℝ) ^ (-E) := by positivity
  have hK0 : (0 : ℝ) ≤ X.KR idx := (X.KR_pos idx).le
  -- combine
  have e : (2 : ℝ) ^ (-(E - 14)) = (2 : ℝ) ^ (-E) * 2 ^ (14 : ℤ) := by
    rw [← zp2]; ring_nf
  calc ((if g ≠ 0 then 1 else 0 : ℕ) * mulTop true (g >>> 31) (g &&& m31) rd.k1s[idx]! rd.k0s[idx]! : ℕ) *
        (2 : ℝ) ^ (-(E - 14))
      ≤ (g : ℝ) * ((rd.k1s[idx]! * 2 ^ 31 + rd.k0s[idx]! : ℕ) : ℝ) / 2 ^ 76 * (2 : ℝ) ^ (-(E - 14)) := by
        gcongr; push_cast at ht ⊢; exact ht
    _ = ((g : ℝ) * (2 : ℝ) ^ (-E)) * (((rd.k1s[idx]! * 2 ^ 31 + rd.k0s[idx]! : ℕ) : ℝ) / 2 ^ 62) := by
        rw [e]; simp only [zpow_ofNat]; ring
    _ ≤ (∑ D ∈ Finset.range 17,
          if X.pt.trans[(D * 2 + ns / 2) * 2 + ns % 2]! = D2 then X.RxF i (c * 17 + D) else 0) * X.KR idx := by
        apply mul_le_mul hgE _ (by positivity) (le_trans hg0 hgE)
        rw [div_le_iff₀ (by positivity)]; linarith
    _ = X.KR idx * ∑ D ∈ Finset.range 17,
          if X.pt.trans[(D * 2 + ns / 2) * 2 + ns % 2]! = D2 then X.RxF i (c * 17 + D) else 0 := by ring

/-- The closing source sum of one target, lower direction. -/
lemma cacc_lower (rd : RecData) (X : ExData) (hc : Compat rd X)
    (hK : ∀ c2 < X.NC, ∀ c < X.NC,
      ((rd.k1s[idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c]! * 2 ^ 31 +
        rd.k0s[idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c]! : ℕ) : ℝ) ≤
        2 ^ 62 * X.KR (idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c))
    (F : Array ℕ) (E : ℤ) (i : ℕ) (hF : ∀ q < X.NC * 17, (F[q]! : ℝ) * (2 : ℝ) ^ (-E) ≤ X.RxF i q)
    {c2 : ℕ} (hc2 : c2 < X.NC) :
    ((accOf true rd F c2).2 : ℝ) * (2 : ℝ) ^ (-(E - 14)) ≤
      ∑ c ∈ Finset.range X.NC, X.KR (idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c) *
        ∑ D ∈ Finset.range 17,
          (X.pt.close2[(D * 2 + X.nsOf c2 c / 2) * 2 + X.nsOf c2 c % 2]! : ℝ) * X.RxF i (c * 17 + D) := by
  obtain ⟨hNR, hNT, hND, hNC, _, _, hcls, hnb, hnbl, hpt, _⟩ := hc
  have hspec := srcLoopF_spec true rd.NR rd.NT rd.ND rd.NC rd.nb[c2 / rd.NT]! (c2 / rd.NT) (c2 % rd.NT)
    rd.k1s rd.k0s rd.cls1 ((GOf rd F).map (· >>> 31)) ((GOf rd F).map (· &&& m31)) ((VOf rd F).map (· >>> 31))
    ((VOf rd F).map (· &&& m31)) (nzOf rd F) rd.NC (Array.replicate 17 0) 0
    (by intro o d hd; simpa using nzOf_lt rd F o d hd)
  unfold accOf
  rw [hspec.2.2, zero_add, Nat.cast_sum, Finset.sum_mul]
  rw [hNR, hNT, hND, hNC]
  apply Finset.sum_le_sum
  intro c hcm
  rw [Finset.mem_range] at hcm
  set idx := idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c with hidx
  set ns := X.nsOf c2 c with hns
  have hns4 : ns < 4 := by
    have := hnbl (c2 / X.NT)
    simp only [hns, ExData.nsOf]; split_ifs <;> omega
  have ho : oOf X.NR X.NT X.ND X.NC rd.nb[c2 / X.NT]! (c2 / X.NT) (c2 % X.NT) rd.cls1 c = ns * X.NC + c := by
    simp only [oOf, hns, ExData.nsOf, hnb, hcls, idx]
  rw [ho]
  have hq : ns * X.NC + c < (VOf rd F).size := by rw [VOf_size, hNC]; nlinarith
  rw [getElem!_map _ _ hq, getElem!_map _ _ hq, VOf_get' rd F hNC hns4 hcm]
  set v := vEntry rd.pt F ns c with hv
  have ht := vterm_lower v rd.k1s[idx]! rd.k0s[idx]!
  have hKc := hK c2 hc2 c hcm
  rw [← hidx] at hKc
  have hvE : (v : ℝ) * (2 : ℝ) ^ (-E) ≤ ∑ D ∈ Finset.range 17,
      (X.pt.close2[(D * 2 + ns / 2) * 2 + ns % 2]! : ℝ) * X.RxF i (c * 17 + D) := by
    rw [hv, vEntry_eq, Nat.cast_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro D hD
    rw [Finset.mem_range] at hD
    rw [hpt]
    push_cast
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hF _ (by nlinarith)) (by positivity)
  have hv0 : (0 : ℝ) ≤ (v : ℝ) * (2 : ℝ) ^ (-E) := by positivity
  have hK0 : (0 : ℝ) ≤ X.KR idx := (X.KR_pos idx).le
  have e : (2 : ℝ) ^ (-(E - 14)) = (2 : ℝ) ^ (-E) * 2 ^ (14 : ℤ) := by
    rw [← zp2]; ring_nf
  have hK2 : ((rd.k1s[idx]! * 2 ^ 31 + rd.k0s[idx]! : ℕ) : ℝ) / 2 ^ 62 ≤ X.KR idx := by
    rw [div_le_iff₀ (by positivity)]; linarith
  calc (mulTop true (v >>> 31) (v &&& m31) rd.k1s[idx]! rd.k0s[idx]! : ℝ) * (2 : ℝ) ^ (-(E - 14))
      ≤ (v : ℝ) * ((rd.k1s[idx]! * 2 ^ 31 + rd.k0s[idx]! : ℕ) : ℝ) / 2 ^ 76 * (2 : ℝ) ^ (-(E - 14)) := by
        gcongr
    _ = ((v : ℝ) * (2 : ℝ) ^ (-E)) * (((rd.k1s[idx]! * 2 ^ 31 + rd.k0s[idx]! : ℕ) : ℝ) / 2 ^ 62) := by
        rw [e]; simp only [zpow_ofNat]; ring
    _ ≤ (∑ D ∈ Finset.range 17,
          (X.pt.close2[(D * 2 + ns / 2) * 2 + ns % 2]! : ℝ) * X.RxF i (c * 17 + D)) * X.KR idx :=
        mul_le_mul hvE hK2 (div_nonneg (Nat.cast_nonneg _) (by norm_num)) (le_trans hv0 hvE)
    _ = X.KR idx * ∑ D ∈ Finset.range 17,
          (X.pt.close2[(D * 2 + ns / 2) * 2 + ns % 2]! : ℝ) * X.RxF i (c * 17 + D) := by ring

lemma accOf_size (lower : Bool) (rd : RecData) (F : Array ℕ) (c2 : ℕ) : (accOf lower rd F c2).1.size = 17 := by
  have hspec := srcLoopF_spec lower rd.NR rd.NT rd.ND rd.NC rd.nb[c2 / rd.NT]! (c2 / rd.NT) (c2 % rd.NT)
    rd.k1s rd.k0s rd.cls1 ((GOf rd F).map (· >>> 31)) ((GOf rd F).map (· &&& m31)) ((VOf rd F).map (· >>> 31))
    ((VOf rd F).map (· &&& m31)) (nzOf rd F) rd.NC (Array.replicate 17 0) 0
    (by intro o d hd; simpa using nzOf_lt rd F o d hd)
  unfold accOf; rw [hspec.1]; simp

lemma recStep_fst_get (lower : Bool) (rd : RecData) (F : Array ℕ) {c2 D2 : ℕ} (hc2 : c2 < rd.NC)
    (hD2 : D2 < 17) :
    (recStep lower rd F).1[c2 * 17 + D2]! = rd.w[c2 / rd.NT]! * (accOf lower rd F c2).1[D2]! := by
  rw [recStep_eq]
  simp only
  have hq : c2 * 17 + D2 < rd.NC * 17 := by nlinarith
  rw [getElem!_ofFn _ hq]
  simp only
  have h1 : (c2 * 17 + D2) / 17 = c2 := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num : 0 < 17), Nat.div_eq_of_lt hD2, zero_add]
  have h2 : (c2 * 17 + D2) % 17 = D2 := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hD2]
  rw [h1, h2]
  unfold rowsOf
  rw [getElem!_ofFn _ hc2]
  unfold tgtOf
  simp only
  rw [getElem!_map _ _ (by rw [accOf_size]; exact hD2)]

lemma recStep_snd (lower : Bool) (rd : RecData) (F : Array ℕ) :
    (recStep lower rd F).2 = ∑ c2 ∈ Finset.range rd.NC, rd.w[c2 / rd.NT]! * (accOf lower rd F c2).2 := by
  rw [recStep_eq]
  simp only
  rw [foldl_add_range, zero_add]
  apply Finset.sum_congr rfl
  intro c2 hc2
  rw [Finset.mem_range] at hc2
  unfold rowsOf
  rw [getElem!_ofFn _ hc2]
  rfl

/-- One step of the recursion, lower direction. -/
theorem recStep_lower (rd : RecData) (X : ExData) (hc : Compat rd X)
    (hK : ∀ c2 < X.NC, ∀ c < X.NC,
      ((rd.k1s[idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c]! * 2 ^ 31 +
        rd.k0s[idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c]! : ℕ) : ℝ) ≤
        2 ^ 62 * X.KR (idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c))
    (F : Array ℕ) (E : ℤ) (i : ℕ) (hF : ∀ q < X.NC * 17, (F[q]! : ℝ) * (2 : ℝ) ^ (-E) ≤ X.RxF i q) :
    (∀ q2 < X.NC * 17, ((recStep true rd F).1[q2]! : ℝ) * (2 : ℝ) ^ (-(E - 14 + PR)) ≤ X.RxF (i + 1) q2) ∧
    ((recStep true rd F).2 : ℝ) * (2 : ℝ) ^ (-(E - 14 + PR + 1)) ≤ X.Clx i := by
  have hNC := hc.NC
  have hNT := hc.NT
  have hw := hc.w
  have ePR : (2 : ℝ) ^ (-(E - 14 + PR)) = (2 : ℝ) ^ (-(E - 14)) / 2 ^ PR := by
    rw [show -(E - 14 + (PR : ℤ)) = -(E - 14) - (PR : ℤ) by ring, zpow_sub₀ two_ne_zero, zpow_natCast]
  constructor
  · intro q2 hq2
    have hc2 : q2 / 17 < X.NC := by omega
    have hD2 : q2 % 17 < 17 := Nat.mod_lt _ (by norm_num)
    have hq : q2 = q2 / 17 * 17 + q2 % 17 := (Nat.div_add_mod' q2 17).symm
    rw [hq, recStep_fst_get true rd F (by rw [hNC]; exact hc2) hD2]
    rw [← hq]
    have ha := acc_lower rd X hc hK F E i hF hc2 hD2
    simp only [ExData.RxF, hq2, ite_true]
    rw [hNT, hw]
    push_cast
    rw [ePR]
    have hwn : (0 : ℝ) ≤ (rd.w[q2 / 17 / X.NT]! : ℝ) / 2 ^ PR := by positivity
    calc (rd.w[q2 / 17 / X.NT]! : ℝ) * ((accOf true rd F (q2 / 17)).1[q2 % 17]! : ℝ) *
          ((2 : ℝ) ^ (-(E - 14)) / 2 ^ PR)
        = ((rd.w[q2 / 17 / X.NT]! : ℝ) / 2 ^ PR) *
            (((accOf true rd F (q2 / 17)).1[q2 % 17]! : ℝ) * (2 : ℝ) ^ (-(E - 14))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ha hwn
  · rw [recStep_snd, Nat.cast_sum, Finset.sum_mul]
    unfold ExData.Clx
    rw [Finset.mul_sum, hNC]
    apply Finset.sum_le_sum
    intro c2 hc2
    rw [Finset.mem_range] at hc2
    have ha := cacc_lower rd X hc hK F E i hF hc2
    rw [hNT, hw]
    push_cast
    have e2 : (2 : ℝ) ^ (-(E - 14 + PR + 1)) = (2 : ℝ) ^ (-(E - 14)) / 2 ^ PR / 2 := by
      rw [show -(E - 14 + (PR : ℤ) + 1) = -(E - 14) - (PR : ℤ) - 1 by ring, zpow_sub₀ two_ne_zero,
        zpow_sub₀ two_ne_zero, zpow_natCast, zpow_one]
    rw [e2]
    have hwn : (0 : ℝ) ≤ (rd.w[c2 / X.NT]! : ℝ) / 2 ^ PR := by positivity
    calc (rd.w[c2 / X.NT]! : ℝ) * ((accOf true rd F c2).2 : ℝ) * ((2 : ℝ) ^ (-(E - 14)) / 2 ^ PR / 2)
        = (1 / 2) * (((rd.w[c2 / X.NT]! : ℝ) / 2 ^ PR) * (((accOf true rd F c2).2 : ℝ) * (2 : ℝ) ^ (-(E - 14)))) := by
          ring
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left ha hwn

/-! ## One step, upper direction -/

lemma term_upper (g k1 k0 : ℕ) (hk : k0 < 2 ^ 31) (hg : g ≠ 0) :
    (g : ℝ) * ((k1 * 2 ^ 31 + k0 : ℕ) : ℝ) / 2 ^ 76 ≤
      ((if g ≠ 0 then 1 else 0 : ℕ) * mulTop false (g >>> 31) (g &&& m31) k1 k0 : ℝ) := by
  simp only [hg, ne_eq, not_false_eq_true, ite_true, Nat.cast_one, one_mul]
  have := le_mulTop_upper (g >>> 31) (g &&& m31) k1 k0 (and_m31_lt g) hk
  rw [← split31 g] at this
  push_cast at this ⊢
  linarith

lemma vterm_upper (v k1 k0 : ℕ) (hk : k0 < 2 ^ 31) :
    (v : ℝ) * ((k1 * 2 ^ 31 + k0 : ℕ) : ℝ) / 2 ^ 76 ≤ (mulTop false (v >>> 31) (v &&& m31) k1 k0 : ℝ) := by
  have := le_mulTop_upper (v >>> 31) (v &&& m31) k1 k0 (and_m31_lt v) hk
  rw [← split31 v] at this
  push_cast at this ⊢
  linarith

/-- The source sum of one target entry, upper direction. -/
lemma acc_upper (rd : RecData) (X : ExData) (hc : Compat rd X)
    (hK : ∀ c2 < X.NC, ∀ c < X.NC,
      2 ^ 62 * X.KR (idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c) ≤
      ((rd.k1s[idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c]! * 2 ^ 31 +
        rd.k0s[idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c]! : ℕ) : ℝ) ∧
      rd.k0s[idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c]! < 2 ^ 31)
    (F : Array ℕ) (E : ℤ) (i : ℕ) (hF : ∀ q < X.NC * 17, X.RxF i q ≤ (F[q]! : ℝ) * (2 : ℝ) ^ (-E))
    {c2 D2 : ℕ} (hc2 : c2 < X.NC) (hD2 : D2 < 17) :
    ∑ c ∈ Finset.range X.NC, X.KR (idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c) *
        ∑ D ∈ Finset.range 17,
          (if X.pt.trans[(D * 2 + X.nsOf c2 c / 2) * 2 + X.nsOf c2 c % 2]! = D2
          then X.RxF i (c * 17 + D) else 0)
      ≤ ((accOf false rd F c2).1[D2]! : ℝ) * (2 : ℝ) ^ (-(E - 14)) := by
  obtain ⟨hNR, hNT, hND, hNC, _, _, hcls, hnb, hnbl, hpt, hw⟩ := hc
  have hwnn : ∀ ir, 0 ≤ X.wR ir := by intro ir; rw [hw]; positivity
  have hspec := srcLoopF_spec false rd.NR rd.NT rd.ND rd.NC rd.nb[c2 / rd.NT]! (c2 / rd.NT) (c2 % rd.NT)
    rd.k1s rd.k0s rd.cls1 ((GOf rd F).map (· >>> 31)) ((GOf rd F).map (· &&& m31)) ((VOf rd F).map (· >>> 31))
    ((VOf rd F).map (· &&& m31)) (nzOf rd F) rd.NC (Array.replicate 17 0) 0
    (by intro o d hd; simpa using nzOf_lt rd F o d hd)
  unfold accOf
  rw [hspec.2.1 D2]
  have hrep : (Array.replicate 17 0 : Array ℕ)[D2]! = 0 := by
    rw [getElem!_pos _ D2 (by simpa using hD2)]; simp
  rw [hrep, zero_add]
  rw [Nat.cast_sum, Finset.sum_mul]
  rw [hNR, hNT, hND, hNC]
  apply Finset.sum_le_sum
  intro c hcm
  rw [Finset.mem_range] at hcm
  set idx := idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c with hidx
  set ns := X.nsOf c2 c with hns
  have hns4 : ns < 4 := by
    have := hnbl (c2 / X.NT)
    simp only [hns, ExData.nsOf]; split_ifs <;> omega
  have ho : oOf X.NR X.NT X.ND X.NC rd.nb[c2 / X.NT]! (c2 / X.NT) (c2 % X.NT) rd.cls1 c = ns * X.NC + c := by
    simp only [oOf, hns, ExData.nsOf, hnb, hcls, idx]
  rw [ho]
  have hq : (ns * X.NC + c) * 17 + D2 < (GOf rd F).size := by rw [GOf_size, hNC]; nlinarith
  rw [getElem!_map _ _ hq, getElem!_map _ _ hq]
  rw [nzOf_count' rd F hNC hns4 hcm hD2, GOf_get' rd F hNC hns4 hcm hD2]
  set g := gEntry rd.pt F ns c D2 with hg
  obtain ⟨hKc, hk0⟩ := hK c2 hc2 c hcm
  rw [← hidx] at hKc hk0
  have hgE : (∑ D ∈ Finset.range 17,
      if X.pt.trans[(D * 2 + ns / 2) * 2 + ns % 2]! = D2 then X.RxF i (c * 17 + D) else 0) ≤
      (g : ℝ) * (2 : ℝ) ^ (-E) := by
    rw [hg, gEntry_eq, Nat.cast_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro D hD
    rw [Finset.mem_range] at hD
    rw [hpt]
    split_ifs
    · exact hF _ (by nlinarith)
    · simp
  have hK0 : (0 : ℝ) ≤ X.KR idx := (X.KR_pos idx).le
  have e : (2 : ℝ) ^ (-(E - 14)) = (2 : ℝ) ^ (-E) * 2 ^ (14 : ℤ) := by
    rw [← zp2]; ring_nf
  have hK2 : X.KR idx ≤ ((rd.k1s[idx]! * 2 ^ 31 + rd.k0s[idx]! : ℕ) : ℝ) / 2 ^ 62 := by
    rw [le_div_iff₀ (by norm_num)]; linarith
  by_cases hg0 : g = 0
  · have : (∑ D ∈ Finset.range 17,
        if X.pt.trans[(D * 2 + ns / 2) * 2 + ns % 2]! = D2 then X.RxF i (c * 17 + D) else 0) ≤ 0 := by
      have := hgE; rw [hg0] at this; simpa using this
    calc X.KR idx * (∑ D ∈ Finset.range 17,
          if X.pt.trans[(D * 2 + ns / 2) * 2 + ns % 2]! = D2 then X.RxF i (c * 17 + D) else 0)
        ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hK0 this
      _ ≤ _ := by positivity
  · have ht := term_upper g rd.k1s[idx]! rd.k0s[idx]! hk0 hg0
    have hsum0 : 0 ≤ ∑ D ∈ Finset.range 17,
        (if X.pt.trans[(D * 2 + ns / 2) * 2 + ns % 2]! = D2 then X.RxF i (c * 17 + D) else 0) := by
      apply Finset.sum_nonneg; intro D _; split_ifs
      · exact X.RxF_nonneg hwnn i _
      · exact le_rfl
    calc X.KR idx * (∑ D ∈ Finset.range 17,
          if X.pt.trans[(D * 2 + ns / 2) * 2 + ns % 2]! = D2 then X.RxF i (c * 17 + D) else 0)
        ≤ (((rd.k1s[idx]! * 2 ^ 31 + rd.k0s[idx]! : ℕ) : ℝ) / 2 ^ 62) * ((g : ℝ) * (2 : ℝ) ^ (-E)) :=
          mul_le_mul hK2 hgE hsum0 (div_nonneg (Nat.cast_nonneg _) (by norm_num))
      _ = (g : ℝ) * ((rd.k1s[idx]! * 2 ^ 31 + rd.k0s[idx]! : ℕ) : ℝ) / 2 ^ 76 * (2 : ℝ) ^ (-(E - 14)) := by
          rw [e]; simp only [zpow_ofNat]; ring
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast ht

/-- The closing source sum of one target, upper direction. -/
lemma cacc_upper (rd : RecData) (X : ExData) (hc : Compat rd X)
    (hK : ∀ c2 < X.NC, ∀ c < X.NC,
      2 ^ 62 * X.KR (idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c) ≤
      ((rd.k1s[idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c]! * 2 ^ 31 +
        rd.k0s[idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c]! : ℕ) : ℝ) ∧
      rd.k0s[idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c]! < 2 ^ 31)
    (F : Array ℕ) (E : ℤ) (i : ℕ) (hF : ∀ q < X.NC * 17, X.RxF i q ≤ (F[q]! : ℝ) * (2 : ℝ) ^ (-E))
    {c2 : ℕ} (hc2 : c2 < X.NC) :
    ∑ c ∈ Finset.range X.NC, X.KR (idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c) *
        ∑ D ∈ Finset.range 17,
          (X.pt.close2[(D * 2 + X.nsOf c2 c / 2) * 2 + X.nsOf c2 c % 2]! : ℝ) * X.RxF i (c * 17 + D)
      ≤ ((accOf false rd F c2).2 : ℝ) * (2 : ℝ) ^ (-(E - 14)) := by
  obtain ⟨hNR, hNT, hND, hNC, _, _, hcls, hnb, hnbl, hpt, hw⟩ := hc
  have hwnn : ∀ ir, 0 ≤ X.wR ir := by intro ir; rw [hw]; positivity
  have hspec := srcLoopF_spec false rd.NR rd.NT rd.ND rd.NC rd.nb[c2 / rd.NT]! (c2 / rd.NT) (c2 % rd.NT)
    rd.k1s rd.k0s rd.cls1 ((GOf rd F).map (· >>> 31)) ((GOf rd F).map (· &&& m31)) ((VOf rd F).map (· >>> 31))
    ((VOf rd F).map (· &&& m31)) (nzOf rd F) rd.NC (Array.replicate 17 0) 0
    (by intro o d hd; simpa using nzOf_lt rd F o d hd)
  unfold accOf
  rw [hspec.2.2, zero_add, Nat.cast_sum, Finset.sum_mul]
  rw [hNR, hNT, hND, hNC]
  apply Finset.sum_le_sum
  intro c hcm
  rw [Finset.mem_range] at hcm
  set idx := idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c with hidx
  set ns := X.nsOf c2 c with hns
  have hns4 : ns < 4 := by
    have := hnbl (c2 / X.NT)
    simp only [hns, ExData.nsOf]; split_ifs <;> omega
  have ho : oOf X.NR X.NT X.ND X.NC rd.nb[c2 / X.NT]! (c2 / X.NT) (c2 % X.NT) rd.cls1 c = ns * X.NC + c := by
    simp only [oOf, hns, ExData.nsOf, hnb, hcls, idx]
  rw [ho]
  have hq : ns * X.NC + c < (VOf rd F).size := by rw [VOf_size, hNC]; nlinarith
  rw [getElem!_map _ _ hq, getElem!_map _ _ hq, VOf_get' rd F hNC hns4 hcm]
  set v := vEntry rd.pt F ns c with hv
  obtain ⟨hKc, hk0⟩ := hK c2 hc2 c hcm
  rw [← hidx] at hKc hk0
  have ht := vterm_upper v rd.k1s[idx]! rd.k0s[idx]! hk0
  have hvE : (∑ D ∈ Finset.range 17,
      (X.pt.close2[(D * 2 + ns / 2) * 2 + ns % 2]! : ℝ) * X.RxF i (c * 17 + D)) ≤ (v : ℝ) * (2 : ℝ) ^ (-E) := by
    rw [hv, vEntry_eq, Nat.cast_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro D hD
    rw [Finset.mem_range] at hD
    rw [hpt]
    push_cast
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hF _ (by nlinarith)) (by positivity)
  have hsum0 : 0 ≤ ∑ D ∈ Finset.range 17,
      (X.pt.close2[(D * 2 + ns / 2) * 2 + ns % 2]! : ℝ) * X.RxF i (c * 17 + D) := by
    apply Finset.sum_nonneg; intro D _
    exact mul_nonneg (Nat.cast_nonneg _) (X.RxF_nonneg hwnn i _)
  have e : (2 : ℝ) ^ (-(E - 14)) = (2 : ℝ) ^ (-E) * 2 ^ (14 : ℤ) := by
    rw [← zp2]; ring_nf
  have hK2 : X.KR idx ≤ ((rd.k1s[idx]! * 2 ^ 31 + rd.k0s[idx]! : ℕ) : ℝ) / 2 ^ 62 := by
    rw [le_div_iff₀ (by norm_num)]; linarith
  calc X.KR idx * (∑ D ∈ Finset.range 17,
        (X.pt.close2[(D * 2 + ns / 2) * 2 + ns % 2]! : ℝ) * X.RxF i (c * 17 + D))
      ≤ (((rd.k1s[idx]! * 2 ^ 31 + rd.k0s[idx]! : ℕ) : ℝ) / 2 ^ 62) * ((v : ℝ) * (2 : ℝ) ^ (-E)) :=
        mul_le_mul hK2 hvE hsum0 (div_nonneg (Nat.cast_nonneg _) (by norm_num))
    _ = (v : ℝ) * ((rd.k1s[idx]! * 2 ^ 31 + rd.k0s[idx]! : ℕ) : ℝ) / 2 ^ 76 * (2 : ℝ) ^ (-(E - 14)) := by
        rw [e]; simp only [zpow_ofNat]; ring
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast ht

/-- One step of the recursion, upper direction. -/
theorem recStep_upper (rd : RecData) (X : ExData) (hc : Compat rd X)
    (hK : ∀ c2 < X.NC, ∀ c < X.NC,
      2 ^ 62 * X.KR (idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c) ≤
      ((rd.k1s[idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c]! * 2 ^ 31 +
        rd.k0s[idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c]! : ℕ) : ℝ) ∧
      rd.k0s[idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c]! < 2 ^ 31)
    (F : Array ℕ) (E : ℤ) (i : ℕ) (hF : ∀ q < X.NC * 17, X.RxF i q ≤ (F[q]! : ℝ) * (2 : ℝ) ^ (-E)) :
    (∀ q2 < X.NC * 17, X.RxF (i + 1) q2 ≤ ((recStep false rd F).1[q2]! : ℝ) * (2 : ℝ) ^ (-(E - 14 + PR))) ∧
    X.Clx i ≤ ((recStep false rd F).2 : ℝ) * (2 : ℝ) ^ (-(E - 14 + PR + 1)) := by
  have hNC := hc.NC
  have hNT := hc.NT
  have hw := hc.w
  have ePR : (2 : ℝ) ^ (-(E - 14 + PR)) = (2 : ℝ) ^ (-(E - 14)) / 2 ^ PR := by
    rw [show -(E - 14 + (PR : ℤ)) = -(E - 14) - (PR : ℤ) by ring, zpow_sub₀ two_ne_zero, zpow_natCast]
  constructor
  · intro q2 hq2
    have hc2 : q2 / 17 < X.NC := by omega
    have hD2 : q2 % 17 < 17 := Nat.mod_lt _ (by norm_num)
    have hq : q2 = q2 / 17 * 17 + q2 % 17 := (Nat.div_add_mod' q2 17).symm
    have ha := acc_upper rd X hc hK F E i hF hc2 hD2
    simp only [ExData.RxF, hq2, ite_true]
    rw [hq, recStep_fst_get false rd F (by rw [hNC]; exact hc2) hD2, ← hq]
    rw [hNT, hw]
    push_cast
    rw [ePR]
    have hwn : (0 : ℝ) ≤ (rd.w[q2 / 17 / X.NT]! : ℝ) / 2 ^ PR := by positivity
    calc (rd.w[q2 / 17 / X.NT]! : ℝ) / 2 ^ PR * _ ≤ ((rd.w[q2 / 17 / X.NT]! : ℝ) / 2 ^ PR) *
            (((accOf false rd F (q2 / 17)).1[q2 % 17]! : ℝ) * (2 : ℝ) ^ (-(E - 14))) :=
          mul_le_mul_of_nonneg_left ha hwn
      _ = _ := by ring
  · rw [recStep_snd, Nat.cast_sum, Finset.sum_mul]
    unfold ExData.Clx
    rw [Finset.mul_sum, hNC]
    apply Finset.sum_le_sum
    intro c2 hc2
    rw [Finset.mem_range] at hc2
    have ha := cacc_upper rd X hc hK F E i hF hc2
    rw [hNT, hw]
    push_cast
    have e2 : (2 : ℝ) ^ (-(E - 14 + PR + 1)) = (2 : ℝ) ^ (-(E - 14)) / 2 ^ PR / 2 := by
      rw [show -(E - 14 + (PR : ℤ) + 1) = -(E - 14) - (PR : ℤ) - 1 by ring, zpow_sub₀ two_ne_zero,
        zpow_sub₀ two_ne_zero, zpow_natCast, zpow_one]
    rw [e2]
    have hwn : (0 : ℝ) ≤ (rd.w[c2 / X.NT]! : ℝ) / 2 ^ PR := by positivity
    calc (1 / 2) * ((rd.w[c2 / X.NT]! : ℝ) / 2 ^ PR * _)
        ≤ (1 / 2) * (((rd.w[c2 / X.NT]! : ℝ) / 2 ^ PR) *
            (((accOf false rd F c2).2 : ℝ) * (2 : ℝ) ^ (-(E - 14)))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left ha hwn
      _ = _ := by ring

/-! ## Normalisation and iteration -/

lemma normF_fst (lower : Bool) (Fn : Array ℕ) :
    (normF lower Fn).1 = Fn.map (fun v => rnd lower v (normF lower Fn).2) := rfl

lemma normF_lower {Fn : Array ℕ} {E' : ℤ} {q : ℕ} (hq : q < Fn.size) :
    (((normF true Fn).1)[q]! : ℝ) * (2 : ℝ) ^ (-(E' - (normF true Fn).2)) ≤ (Fn[q]! : ℝ) * (2 : ℝ) ^ (-E') := by
  rw [normF_fst, getElem!_map _ _ hq]
  set sh := (normF true Fn).2
  have h := rnd_lower_le Fn[q]! sh
  have e : (2 : ℝ) ^ (-(E' - (sh : ℤ))) = (2 : ℝ) ^ (-E') * 2 ^ sh := by
    rw [show -(E' - (sh : ℤ)) = -E' + (sh : ℤ) by ring, zp2, zpow_natCast]
  rw [e]
  have hp : (0 : ℝ) < 2 ^ sh := by positivity
  have hE : (0 : ℝ) < 2 ^ (-E') := by positivity
  calc (rnd true Fn[q]! sh : ℝ) * ((2 : ℝ) ^ (-E') * 2 ^ sh)
      = ((rnd true Fn[q]! sh : ℝ) * 2 ^ sh) * 2 ^ (-E') := by ring
    _ ≤ (Fn[q]! : ℝ) * 2 ^ (-E') := by
        apply mul_le_mul_of_nonneg_right _ hE.le
        rw [le_div_iff₀ hp] at h; linarith

lemma normF_upper {Fn : Array ℕ} {E' : ℤ} {q : ℕ} (hq : q < Fn.size) :
    (Fn[q]! : ℝ) * (2 : ℝ) ^ (-E') ≤ (((normF false Fn).1)[q]! : ℝ) * (2 : ℝ) ^ (-(E' - (normF false Fn).2)) := by
  rw [normF_fst, getElem!_map _ _ hq]
  set sh := (normF false Fn).2
  have h := le_rnd_upper Fn[q]! sh
  have e : (2 : ℝ) ^ (-(E' - (sh : ℤ))) = (2 : ℝ) ^ (-E') * 2 ^ sh := by
    rw [show -(E' - (sh : ℤ)) = -E' + (sh : ℤ) by ring, zp2, zpow_natCast]
  rw [e]
  have hp : (0 : ℝ) < 2 ^ sh := by positivity
  have hE : (0 : ℝ) < 2 ^ (-E') := by positivity
  calc (Fn[q]! : ℝ) * 2 ^ (-E') ≤ ((rnd false Fn[q]! sh : ℝ) * 2 ^ sh) * 2 ^ (-E') := by
        apply mul_le_mul_of_nonneg_right _ hE.le
        rw [div_le_iff₀ hp] at h; linarith
    _ = _ := by ring

lemma normF_size (lower : Bool) (Fn : Array ℕ) : (normF lower Fn).1.size = Fn.size := by
  rw [normF_fst]; simp

lemma recStep_fst_size (lower : Bool) (rd : RecData) (F : Array ℕ) : (recStep lower rd F).1.size = rd.NC * 17 := by
  rw [recStep_eq]; simp

/-- The iteration, lower direction: every appended `(psi, scale)` bounds the matching closing sum. -/
theorem recIter_lower (rd : RecData) (X : ExData) (hc : Compat rd X)
    (hK : ∀ c2 < X.NC, ∀ c < X.NC,
      ((rd.k1s[idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c]! * 2 ^ 31 +
        rd.k0s[idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c]! : ℕ) : ℝ) ≤
        2 ^ 62 * X.KR (idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c)) :
    ∀ (n i : ℕ) (F : Array ℕ) (E : ℤ) (out : List (ℕ × ℤ)),
      (∀ q < X.NC * 17, (F[q]! : ℝ) * (2 : ℝ) ^ (-E) ≤ X.RxF i q) →
      (recIter true rd n F E out).length = out.length + n ∧
      (recIter true rd n F E out).take out.length = out ∧
      ∀ m < n, ((recIter true rd n F E out)[out.length + m]!.1 : ℝ) *
        (2 : ℝ) ^ (-(recIter true rd n F E out)[out.length + m]!.2) ≤ X.Clx (i + m) := by
  intro n
  induction n with
  | zero => intro i F E out _; simp [recIter]
  | succ n ih =>
    intro i F E out hF
    have hstep := recStep_lower rd X hc hK F E i hF
    set Fn := (recStep true rd F).1
    set psi := (recStep true rd F).2
    have hFn : ∀ q < X.NC * 17, ((normF true Fn).1[q]! : ℝ) *
        (2 : ℝ) ^ (-(E - 14 + PR - (normF true Fn).2)) ≤ X.RxF (i + 1) q := by
      intro q hq
      have hqs : q < Fn.size := by rw [recStep_fst_size, hc.NC]; exact hq
      exact le_trans (normF_lower hqs) (hstep.1 q hq)
    have ih' := ih (i + 1) (normF true Fn).1 (E - 14 + PR - (normF true Fn).2) (out ++ [(psi, E - 14 + PR + 1)]) hFn
    have e : recIter true rd (n + 1) F E out =
        recIter true rd n (normF true Fn).1 (E - 14 + PR - (normF true Fn).2) (out ++ [(psi, E - 14 + PR + 1)]) := rfl
    rw [e]
    simp only [List.length_append, List.length_singleton] at ih'
    refine ⟨by rw [ih'.1]; ring, ?_, ?_⟩
    · have h2 := ih'.2.1
      set L := recIter true rd n (normF true Fn).1 (E - 14 + PR - (normF true Fn).2) (out ++ [(psi, E - 14 + PR + 1)])
      have : L.take out.length = (L.take (out.length + 1)).take out.length := by
        rw [List.take_take, min_eq_left (by omega)]
      rw [this, h2]
      simp
    · intro m hm
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0
        have h2 := ih'.2.1
        set L' := recIter true rd n (normF true Fn).1 (E - 14 + PR - (normF true Fn).2)
          (out ++ [(psi, E - 14 + PR + 1)]) with hL'
        have hget : L'[out.length]! = (psi, E - 14 + PR + 1) := by
          have h3 : L'[out.length]? = some (psi, E - 14 + PR + 1) := by
            have := congrArg (fun l : List (ℕ × ℤ) => l[out.length]?) h2
            simp only [List.getElem?_take_of_lt (show out.length < out.length + 1 by omega)] at this
            rw [this]; simp
          rw [List.getElem!_eq_getElem?_getD, h3]; rfl
        simp only [add_zero]
        rw [hget]
        exact hstep.2
      · have := ih'.2.2 (m - 1) (by omega)
        rw [show out.length + 1 + (m - 1) = out.length + m by omega] at this
        rw [show i + 1 + (m - 1) = i + m by omega] at this
        exact this

/-- The iteration, upper direction. -/
theorem recIter_upper (rd : RecData) (X : ExData) (hc : Compat rd X)
    (hK : ∀ c2 < X.NC, ∀ c < X.NC,
      2 ^ 62 * X.KR (idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c) ≤
      ((rd.k1s[idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c]! * 2 ^ 31 +
        rd.k0s[idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c]! : ℕ) : ℝ) ∧
      rd.k0s[idxOf X.NR X.NT X.ND (c2 / X.NT) (c2 % X.NT) c]! < 2 ^ 31) :
    ∀ (n i : ℕ) (F : Array ℕ) (E : ℤ) (out : List (ℕ × ℤ)),
      (∀ q < X.NC * 17, X.RxF i q ≤ (F[q]! : ℝ) * (2 : ℝ) ^ (-E)) →
      (recIter false rd n F E out).length = out.length + n ∧
      (recIter false rd n F E out).take out.length = out ∧
      ∀ m < n, X.Clx (i + m) ≤ ((recIter false rd n F E out)[out.length + m]!.1 : ℝ) *
        (2 : ℝ) ^ (-(recIter false rd n F E out)[out.length + m]!.2) := by
  intro n
  induction n with
  | zero => intro i F E out _; simp [recIter]
  | succ n ih =>
    intro i F E out hF
    have hstep := recStep_upper rd X hc hK F E i hF
    set Fn := (recStep false rd F).1
    set psi := (recStep false rd F).2
    have hFn : ∀ q < X.NC * 17, X.RxF (i + 1) q ≤ ((normF false Fn).1[q]! : ℝ) *
        (2 : ℝ) ^ (-(E - 14 + PR - (normF false Fn).2)) := by
      intro q hq
      have hqs : q < Fn.size := by rw [recStep_fst_size, hc.NC]; exact hq
      exact le_trans (hstep.1 q hq) (normF_upper hqs)
    have ih' := ih (i + 1) (normF false Fn).1 (E - 14 + PR - (normF false Fn).2) (out ++ [(psi, E - 14 + PR + 1)]) hFn
    have e : recIter false rd (n + 1) F E out =
        recIter false rd n (normF false Fn).1 (E - 14 + PR - (normF false Fn).2) (out ++ [(psi, E - 14 + PR + 1)]) := rfl
    rw [e]
    simp only [List.length_append, List.length_singleton] at ih'
    refine ⟨by rw [ih'.1]; ring, ?_, ?_⟩
    · have h2 := ih'.2.1
      set L := recIter false rd n (normF false Fn).1 (E - 14 + PR - (normF false Fn).2) (out ++ [(psi, E - 14 + PR + 1)])
      have : L.take out.length = (L.take (out.length + 1)).take out.length := by
        rw [List.take_take, min_eq_left (by omega)]
      rw [this, h2]
      simp
    · intro m hm
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0
        have h2 := ih'.2.1
        set L' := recIter false rd n (normF false Fn).1 (E - 14 + PR - (normF false Fn).2)
          (out ++ [(psi, E - 14 + PR + 1)]) with hL'
        have hget : L'[out.length]! = (psi, E - 14 + PR + 1) := by
          have h3 : L'[out.length]? = some (psi, E - 14 + PR + 1) := by
            have := congrArg (fun l : List (ℕ × ℤ) => l[out.length]?) h2
            simp only [List.getElem?_take_of_lt (show out.length < out.length + 1 by omega)] at this
            rw [this]; simp
          rw [List.getElem!_eq_getElem?_getD, h3]; rfl
        simp only [add_zero]
        rw [hget]
        exact hstep.2
      · have := ih'.2.2 (m - 1) (by omega)
        rw [show out.length + 1 + (m - 1) = out.length + m by omega] at this
        rw [show i + 1 + (m - 1) = i + m by omega] at this
        exact this

end BHH.W2
