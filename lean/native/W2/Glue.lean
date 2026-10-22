/-
From the production checks to the bound: the meaning of `shardOK = true` (claimed enclosures of `Ψ^d_k(t_j)` for the
table data of the run), the log helpers of the t-integral, `claimLogs`, `tintOK = true`, and the assembly of
`Σ_{k=6}^{kmax} C_k ≥ num/den` from the modules L, D, T, the table soundness and the recursion soundness.
-/
import W2.RunData
import W2.Interfaces
import W2.Laplace
import W2.Disc
import W2.FixSound

open MeasureTheory Set Real
open scoped ENNReal

namespace BHH.W2

open W2C BHH.Cert BHH

/-! ## Scaled comparisons and the claim checks -/

lemma two_zpow_toNat {a : ℤ} (ha : 0 ≤ a) : (2 : ℝ) ^ a.toNat = (2 : ℝ) ^ a := by
  rw [← zpow_natCast, Int.toNat_of_nonneg ha]

lemma leScaled_spec {a : ℕ} {ea : ℤ} {b : ℕ} {eb : ℤ} (h : leScaled a ea b eb = true) :
    (a : ℝ) * 2 ^ (-ea) ≤ (b : ℝ) * 2 ^ (-eb) := by
  unfold leScaled at h
  simp only [decide_eq_true_eq] at h
  have h1 : 0 ≤ eb - min ea eb := by omega
  have h2 : 0 ≤ ea - min ea eb := by omega
  have hR : (a : ℝ) * 2 ^ (eb - min ea eb) ≤ (b : ℝ) * 2 ^ (ea - min ea eb) := by
    rw [← two_zpow_toNat h1, ← two_zpow_toNat h2]
    exact_mod_cast h
  have hpos : (0 : ℝ) < 2 ^ (min ea eb - ea - eb) := zpow_pos (by norm_num) _
  have e1 : (a : ℝ) * 2 ^ (-ea) = (a : ℝ) * 2 ^ (eb - min ea eb) * 2 ^ (min ea eb - ea - eb) := by
    rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 2; ring
  have e2 : (b : ℝ) * 2 ^ (-eb) = (b : ℝ) * 2 ^ (ea - min ea eb) * 2 ^ (min ea eb - ea - eb) := by
    rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 2; ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right hR hpos.le

/-- A claim entry `(k, loM, loE, hiM, hiE)`. -/
abbrev CEntry := ℕ × ℕ × ℤ × ℕ × ℤ

lemma checkClaims_spec {kmax : ℕ} {lo hi : Array (ℕ × ℤ)} {c : TClaim} (h : checkClaims kmax lo hi c = true) :
    1 ≤ c.1 ∧ ∀ e ∈ c.2, 3 ≤ e.1 ∧ e.1 ≤ kmax ∧
      (e.2.1 : ℝ) * 2 ^ (-e.2.2.1) ≤ (lo[e.1 - 3]!.1 : ℝ) * 2 ^ (-lo[e.1 - 3]!.2) ∧
      (hi[e.1 - 3]!.1 : ℝ) * 2 ^ (-hi[e.1 - 3]!.2) ≤ (e.2.2.2.1 : ℝ) * 2 ^ (-e.2.2.2.2) := by
  obtain ⟨j, lst⟩ := c
  unfold checkClaims at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  refine ⟨h.1, fun e he => ?_⟩
  obtain ⟨k, lm, le, hm, he'⟩ := e
  have h2 := h.2 _ he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  obtain ⟨⟨hk3, hkm⟩, hrest⟩ := h2
  rcases hlo : lo[k - 3]! with ⟨pl, sl⟩
  rcases hhi : hi[k - 3]! with ⟨ph, sh⟩
  rw [hlo, hhi] at hrest
  simp only [Bool.and_eq_true] at hrest
  exact ⟨hk3, hkm, leScaled_spec hrest.1, leScaled_spec hrest.2⟩

lemma shardOK_spec {g : Grid} {dtl kmax : ℕ} {cs : List TClaim} (h : shardOK g dtl kmax true cs = true) :
    ∀ c ∈ cs, checkClaims kmax
      (runT4 g (mkRunData g dtl true).rings (mkRunData g dtl true).tab (mkRunData g dtl true).e1lo mkPassTab true
        c.1 dtl kmax).toArray
      (runT4 g (mkRunData g dtl true).rings (mkRunData g dtl true).tab (mkRunData g dtl true).e1hi mkPassTab false
        c.1 dtl kmax).toArray c = true := by
  unfold shardOK at h
  simp only [if_true, List.all_map, List.all_eq_true] at h
  intro c hc
  exact h c hc

/-- The claimed enclosures of a checked shard bound `Ψ^d_k(t_j)` for the table data of the run. -/
theorem claim_psid {g : Grid} {dtl kmax : ℕ} {cs : List TClaim}
    (hsh : ∀ c ∈ cs, checkClaims kmax
      (runT4 g (mkRunData g dtl true).rings (mkRunData g dtl true).tab (mkRunData g dtl true).e1lo mkPassTab true
        c.1 dtl kmax).toArray
      (runT4 g (mkRunData g dtl true).rings (mkRunData g dtl true).tab (mkRunData g dtl true).e1hi mkPassTab false
        c.1 dtl kmax).toArray c = true)
    (hNR : 0 < (gR g).NR) (hNT : 0 < (gR g).NT)
    (hub : ∀ ir : ℕ, 0 ≤ ubInt (mkRunData g dtl true).rings[ir]!.euHi dtl) :
    ∀ c ∈ cs, 1 ≤ c.1 ∧ ∀ e ∈ c.2, 3 ≤ e.1 ∧ e.1 ≤ kmax ∧
      (e.2.1 : ℝ) * 2 ^ (-e.2.2.1) ≤
        Psid (gR g) hNR hNT (discOf g (mkRunData g dtl true).rings (mkRunData g dtl true).tab dtl) (e.1 - 1)
          ((c.1 : ℝ) / 2 ^ dtl) ∧
      Psid (gR g) hNR hNT (discOf g (mkRunData g dtl true).rings (mkRunData g dtl true).tab dtl) (e.1 - 1)
          ((c.1 : ℝ) / 2 ^ dtl) ≤ (e.2.2.2.1 : ℝ) * 2 ^ (-e.2.2.2.2) := by
  intro c hc
  have hcc := checkClaims_spec (hsh c hc)
  refine ⟨hcc.1, fun e he => ?_⟩
  obtain ⟨hk3, hkm, hlo, hhi⟩ := hcc.2 e he
  have hin := runInputs_mk g hNT dtl true
  have hm : e.1 - 3 < kmax - 2 := by omega
  have hidx : e.1 - 3 + 2 = e.1 - 1 := by omega
  have hA := clx_eq_psid (tab := (mkRunData g dtl true).tab) hin.rings_size hNR hNT c.1 dtl (e.1 - 3)
  rw [hidx] at hA
  have hL := runT4_lower hin mkPassTab c.1 kmax (e.1 - 3) hm
  have hU := runT4_upper hin hub mkPassTab c.1 kmax (e.1 - 3) hm
  rw [hA] at hL hU
  rw [List.getElem!_toArray] at hlo hhi
  exact ⟨hk3, hkm, hlo.trans hL, hU.trans hhi⟩

/-! ## The log helpers -/

lemma fx_add_mul (a e b : ℤ) : fx (a + e * b) = fx a + e * fx b := by
  unfold fx; push_cast; ring

lemma log2Iv_spec : fx log2Iv.lo ≤ Real.log 2 ∧ Real.log 2 ≤ fx log2Iv.hi := by
  have h2 : fx (2 * ONE) = 2 := by
    unfold fx; rw [show ((2 * ONE : ℤ) : ℝ) = 2 * 2 ^ PR by norm_num [ONE, PR]]; field_simp
  have hpos : (0 : ℤ) < 2 * ONE := by simp [ONE, PR]
  constructor
  · have := logLo_spec (2 * ONE) hpos
    rw [h2] at this
    exact this
  · have := logHi_spec (2 * ONE) hpos (by simp [ONE, PR])
    rw [h2] at this
    exact this

lemma nbitsN_spec {m : ℕ} (hm : 0 < m) : 2 ^ (nbitsN m - 1) ≤ m ∧ m < 2 ^ nbitsN m := by
  unfold nbitsN
  rw [Nat.add_sub_cancel]
  exact ⟨Nat.log2_self_le (by omega), Nat.lt_log2_self⟩

lemma fx_natCast (n : ℕ) : fx ((n : ℕ) : ℤ) = (n : ℝ) / 2 ^ PR := by
  unfold fx; push_cast; ring

/-- The mantissa of `logScaled`: `x 2^-PR` is `m 2^-b` rounded in the direction of the bound, `0 < x ≤ 2^PR`. -/
lemma logScaled_mant (lower : Bool) {m : ℕ} (hm : 0 < m) :
    let b := nbitsN m
    let x : ℤ := if b ≤ PR then ((m * 2 ^ (PR - b) : ℕ) : ℤ)
      else if lower then ((m >>> (b - PR) : ℕ) : ℤ) else (((m + 2 ^ (b - PR) - 1) >>> (b - PR) : ℕ) : ℤ)
    0 < x ∧ x ≤ 2 ^ PR ∧ (lower = true → fx x ≤ (m : ℝ) / 2 ^ b) ∧ (lower = false → (m : ℝ) / 2 ^ b ≤ fx x) := by
  intro b x
  have hPR : PR = 96 := rfl
  obtain ⟨hb1, hb2⟩ := nbitsN_spec hm
  have hb : 1 ≤ b := by
    show 1 ≤ nbitsN m
    unfold nbitsN; omega
  by_cases hbp : b ≤ PR
  · have hx : x = ((m * 2 ^ (PR - b) : ℕ) : ℤ) := if_pos hbp
    have hfx : fx x = (m : ℝ) / 2 ^ b := by
      rw [hx, fx_natCast]; push_cast
      rw [pow_sub₀ (2 : ℝ) (by norm_num) hbp]; field_simp
    refine ⟨?_, ?_, fun _ => hfx.le, fun _ => hfx.ge⟩
    · rw [hx]; positivity
    · rw [hx]
      have : m * 2 ^ (PR - b) ≤ 2 ^ PR := by
        have h1 : m * 2 ^ (PR - b) < 2 ^ b * 2 ^ (PR - b) := Nat.mul_lt_mul_of_pos_right hb2 (by positivity)
        rw [← pow_add, Nat.add_sub_cancel' hbp] at h1
        omega
      exact_mod_cast this
  · push_neg at hbp
    set s := b - PR with hs
    have hsb : b = PR + s := by omega
    have hm2 : 2 ^ (PR - 1) * 2 ^ s ≤ m := by
      rw [← pow_add]
      calc 2 ^ (PR - 1 + s) = 2 ^ (b - 1) := by congr 1; omega
        _ ≤ m := hb1
    have hm3 : m < 2 ^ PR * 2 ^ s := by rw [← pow_add, ← hsb]; exact hb2
    have hs1 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
    have hq1 : 2 ^ (PR - 1) ≤ m / 2 ^ s := (Nat.le_div_iff_mul_le (by positivity)).mpr hm2
    have hq2 : m / 2 ^ s < 2 ^ PR := (Nat.div_lt_iff_lt_mul (by positivity)).mpr hm3
    have hP1 : 0 < 2 ^ (PR - 1) := by positivity
    have hden : (m : ℝ) / 2 ^ b = (m : ℝ) / (2 ^ PR * 2 ^ s) := by rw [hsb, pow_add]
    cases lower with
    | true =>
      have hx : x = ((m / 2 ^ s : ℕ) : ℤ) := by
        show (if b ≤ PR then _ else if true = true then _ else _) = _
        rw [if_neg (by omega), if_pos rfl, Nat.shiftRight_eq_div_pow]
      refine ⟨?_, ?_, fun _ => ?_, fun h => absurd h (by decide)⟩
      · rw [hx]; exact_mod_cast (show 0 < m / 2 ^ s by omega)
      · rw [hx]; exact_mod_cast hq2.le
      · rw [hx, fx_natCast, hden, div_le_div_iff₀ (by positivity) (by positivity)]
        have hdm : (m / 2 ^ s) * 2 ^ s ≤ m := Nat.div_mul_le_self m (2 ^ s)
        have h3 : ((m / 2 ^ s : ℕ) : ℝ) * 2 ^ s ≤ (m : ℝ) := by exact_mod_cast hdm
        calc ((m / 2 ^ s : ℕ) : ℝ) * (2 ^ PR * 2 ^ s) = (((m / 2 ^ s : ℕ) : ℝ) * 2 ^ s) * 2 ^ PR := by ring
          _ ≤ (m : ℝ) * 2 ^ PR := mul_le_mul_of_nonneg_right h3 (by positivity)
    | false =>
      have hx : x = (((m + 2 ^ s - 1) / 2 ^ s : ℕ) : ℤ) := by
        show (if b ≤ PR then _ else if false = true then _ else _) = _
        rw [if_neg (by omega), if_neg (by decide), Nat.shiftRight_eq_div_pow]
      have hc1 : m / 2 ^ s ≤ (m + 2 ^ s - 1) / 2 ^ s := Nat.div_le_div_right (by omega)
      have hc2 : (m + 2 ^ s - 1) / 2 ^ s < 2 ^ PR + 1 := by
        apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
        rw [Nat.add_mul, one_mul]
        omega
      refine ⟨?_, ?_, fun h => absurd h (by decide), fun _ => ?_⟩
      · rw [hx]; exact_mod_cast (show 0 < (m + 2 ^ s - 1) / 2 ^ s by omega)
      · rw [hx]; exact_mod_cast (show (m + 2 ^ s - 1) / 2 ^ s ≤ 2 ^ PR by omega)
      · rw [hx, fx_natCast, hden, div_le_div_iff₀ (by positivity) (by positivity)]
        have hdm : m ≤ ((m + 2 ^ s - 1) / 2 ^ s) * 2 ^ s := by
          have := Nat.lt_div_mul_add (a := m + 2 ^ s - 1) (b := 2 ^ s) (by positivity)
          omega
        have h3 : (m : ℝ) ≤ (((m + 2 ^ s - 1) / 2 ^ s : ℕ) : ℝ) * 2 ^ s := by exact_mod_cast hdm
        calc (m : ℝ) * 2 ^ PR ≤ ((((m + 2 ^ s - 1) / 2 ^ s : ℕ) : ℝ) * 2 ^ s) * 2 ^ PR :=
              mul_le_mul_of_nonneg_right h3 (by positivity)
          _ = (((m + 2 ^ s - 1) / 2 ^ s : ℕ) : ℝ) * (2 ^ PR * 2 ^ s) := by ring

lemma log_scaled_split {m : ℕ} (hm : 0 < m) (sc : ℤ) :
    Real.log ((m : ℝ) * 2 ^ (-sc)) = Real.log ((m : ℝ) / 2 ^ nbitsN m) + (((nbitsN m : ℤ) - sc : ℤ) : ℝ) * Real.log 2 := by
  have hX : (m : ℝ) * 2 ^ (-sc) = ((m : ℝ) / 2 ^ nbitsN m) * 2 ^ ((nbitsN m : ℤ) - sc) := by
    rw [zpow_sub₀ (two_ne_zero), zpow_neg, zpow_natCast]
    field_simp
  have hmb : (0 : ℝ) < (m : ℝ) / 2 ^ nbitsN m := by positivity
  rw [hX, Real.log_mul hmb.ne' (by positivity), Real.log_zpow]

lemma l2_lo (e : ℤ) {inst : Decidable ((0 ≤ e) = (true = true))} :
    (e : ℝ) * fx (@ite _ ((0 ≤ e) = (true = true)) inst log2Iv.lo log2Iv.hi) ≤ (e : ℝ) * Real.log 2 := by
  by_cases he : 0 ≤ e
  · rw [if_pos (propext ⟨fun _ => rfl, fun _ => he⟩)]
    exact mul_le_mul_of_nonneg_left log2Iv_spec.1 (by exact_mod_cast he)
  · rw [if_neg (fun h => he (cast h.symm rfl))]
    push_neg at he
    exact mul_le_mul_of_nonpos_left log2Iv_spec.2 (by exact_mod_cast he.le)

lemma l2_hi (e : ℤ) {inst : Decidable ((0 ≤ e) = (false = true))} :
    (e : ℝ) * Real.log 2 ≤ (e : ℝ) * fx (@ite _ ((0 ≤ e) = (false = true)) inst log2Iv.lo log2Iv.hi) := by
  by_cases he : 0 ≤ e
  · rw [if_neg (fun h => absurd (cast h he) (by decide))]
    exact mul_le_mul_of_nonneg_left log2Iv_spec.2 (by exact_mod_cast he)
  · rw [if_pos (propext ⟨fun h => absurd h he, fun h => absurd h (by decide)⟩)]
    push_neg at he
    exact mul_le_mul_of_nonpos_left log2Iv_spec.1 (by exact_mod_cast he.le)

theorem logScaled_lo {m : ℕ} (hm : 0 < m) (sc : ℤ) :
    fx (logScaled true m sc) ≤ Real.log ((m : ℝ) * 2 ^ (-sc)) := by
  obtain ⟨hx0, hx1, hxl, -⟩ := logScaled_mant true hm
  set b := nbitsN m with hb
  set x : ℤ := if b ≤ PR then ((m * 2 ^ (PR - b) : ℕ) : ℤ)
      else if true = true then ((m >>> (b - PR) : ℕ) : ℤ) else (((m + 2 ^ (b - PR) - 1) >>> (b - PR) : ℕ) : ℤ)
    with hxdef
  have e : logScaled true m sc = logLo x + ((b : ℤ) - sc) *
      (if (0 ≤ (b : ℤ) - sc) = (true = true) then log2Iv.lo else log2Iv.hi) := rfl
  rw [e, fx_add_mul, log_scaled_split hm sc, ← hb]
  have hfx0 : 0 < fx x := by unfold fx; positivity
  have h1 : fx (logLo x) ≤ Real.log ((m : ℝ) / 2 ^ b) :=
    (logLo_spec x hx0).trans (Real.log_le_log hfx0 (hxl rfl))
  exact add_le_add h1 (l2_lo _)

theorem logScaled_hi {m : ℕ} (hm : 0 < m) (sc : ℤ) :
    Real.log ((m : ℝ) * 2 ^ (-sc)) ≤ fx (logScaled false m sc) := by
  obtain ⟨hx0, hx1, -, hxu⟩ := logScaled_mant false hm
  set b := nbitsN m with hb
  set x : ℤ := if b ≤ PR then ((m * 2 ^ (PR - b) : ℕ) : ℤ)
      else if false = true then ((m >>> (b - PR) : ℕ) : ℤ) else (((m + 2 ^ (b - PR) - 1) >>> (b - PR) : ℕ) : ℤ)
    with hxdef
  have e : logScaled false m sc = logHi x + ((b : ℤ) - sc) *
      (if (0 ≤ (b : ℤ) - sc) = (false = true) then log2Iv.lo else log2Iv.hi) := rfl
  rw [e, fx_add_mul, log_scaled_split hm sc, ← hb]
  have hmb : (0 : ℝ) < (m : ℝ) / 2 ^ b := by positivity
  have hx2 : x ≤ 2 ^ 200 := hx1.trans (by norm_num [PR])
  have h1 : Real.log ((m : ℝ) / 2 ^ b) ≤ fx (logHi x) :=
    (Real.log_le_log hmb (hxu rfl)).trans (logHi_spec x hx0 hx2)
  exact add_le_add h1 (l2_hi _)

lemma logTable_size (n q : ℕ) : (logTable n q).size = n + 1 := by
  unfold logTable; simp

theorem logTable_spec (n q : ℕ) {i : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ n) :
    fx (logTable n q)[i]! ≤ Real.log ((i : ℝ) / 2 ^ q) := by
  unfold logTable
  rw [getElem!_map _ _ (by simp; omega), range_getElem! (by omega)]
  rw [if_neg (by simp; omega)]
  have := logScaled_lo (m := i) (by omega) (q : ℤ)
  rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv] at this
  exact this

/-! ## The claim table `claimLogs` -/

/-- An entry `v` of the claim table at `(k, j)` comes from a claim with a positive lower mantissa. -/
def EntryOK (cs : List TClaim) (k j : ℕ) (v : ℤ × ℤ) : Prop :=
  ∃ c ∈ cs, ∃ e ∈ c.2, c.1 = j ∧ e.1 = k ∧ 0 < e.2.1 ∧
    v = (logScaled true e.2.1 e.2.2.1, logScaled false e.2.2.2.1 e.2.2.2.2)

/-- The invariant of the fold building the claim table. -/
structure FillInv (cs : List TClaim) (kmax ntv : ℕ) (acc : Array (Array (Option (ℤ × ℤ)))) : Prop where
  size : acc.size = kmax + 1
  rows : ∀ k < kmax + 1, acc[k]!.size = ntv + 1
  ok : ∀ k j v, (acc[k]!)[j]! = some v → EntryOK cs k j v

lemma modify_getElem! {α : Type*} [Inhabited α] (a : Array α) (k k' : ℕ) (f : α → α) (hk' : k' < a.size) :
    (a.modify k f)[k']! = if k = k' then f a[k']! else a[k']! := by
  rw [getElem!_pos (a.modify k f) k' (by simpa using hk'), getElem!_pos a k' hk', Array.getElem_modify]

lemma modify_getElem!_ge {α : Type*} [Inhabited α] (a : Array α) (k k' : ℕ) (f : α → α) (hk' : a.size ≤ k') :
    (a.modify k f)[k']! = default := by
  rw [getElem!_neg (a.modify k f) k' (by simp; omega)]

lemma default_arr_getElem! (j : ℕ) : (default : Array (Option (ℤ × ℤ)))[j]! = none := by
  rw [getElem!_neg _ j (by simp [show (default : Array (Option (ℤ × ℤ))) = #[] from rfl])]
  rfl

lemma fillInv_step {cs : List TClaim} {kmax ntv : ℕ} {acc : Array (Array (Option (ℤ × ℤ)))}
    (hacc : FillInv cs kmax ntv acc) {c : TClaim} (hc : c ∈ cs) {e : CEntry} (he : e ∈ c.2) :
    FillInv cs kmax ntv
      (if e.1 ≤ kmax ∧ 1 ≤ c.1 ∧ c.1 ≤ ntv ∧ 0 < e.2.1 then
        acc.modify e.1 (·.set! c.1 (some (logScaled true e.2.1 e.2.2.1, logScaled false e.2.2.2.1 e.2.2.2.2)))
      else acc) := by
  split_ifs with hcond
  · obtain ⟨hk, hj1, hj2, hlm⟩ := hcond
    refine ⟨by rw [Array.size_modify, hacc.size], fun k' hk' => ?_, fun k' j' v hv => ?_⟩
    · rw [modify_getElem! _ _ _ _ (by rw [hacc.size]; exact hk')]
      split_ifs with h
      · rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hacc.rows k' hk']
      · exact hacc.rows k' hk'
    · by_cases hk' : k' < acc.size
      · rw [modify_getElem! _ _ _ _ hk'] at hv
        split_ifs at hv with h
        · subst h
          have hrow := hacc.rows e.1 (by rw [← hacc.size]; exact hk')
          by_cases hj : c.1 = j'
          · subst hj
            rw [Array.getElem!_set!_self _ _ _ (by rw [hrow]; omega)] at hv
            exact ⟨c, hc, e, he, rfl, rfl, hlm, (Option.some.inj hv).symm⟩
          · rw [Array.getElem!_set!_ne _ _ _ _ hj] at hv
            exact hacc.ok _ _ _ hv
        · exact hacc.ok _ _ _ hv
      · push_neg at hk'
        rw [modify_getElem!_ge _ _ _ _ hk', default_arr_getElem!] at hv
        exact absurd hv (by simp)
  · exact hacc

lemma fillInv_inner {cs : List TClaim} {kmax ntv : ℕ} {c : TClaim} (hc : c ∈ cs) :
    ∀ (lst : List CEntry), (∀ e ∈ lst, e ∈ c.2) → ∀ acc, FillInv cs kmax ntv acc →
      FillInv cs kmax ntv (lst.foldl (fun acc2 (e : CEntry) =>
        if e.1 ≤ kmax ∧ 1 ≤ c.1 ∧ c.1 ≤ ntv ∧ 0 < e.2.1 then
          acc2.modify e.1 (·.set! c.1 (some (logScaled true e.2.1 e.2.2.1, logScaled false e.2.2.2.1 e.2.2.2.2)))
        else acc2) acc)
  | [], _, acc, h => h
  | e :: rest, hsub, acc, h => by
    rw [List.foldl_cons]
    exact fillInv_inner hc rest (fun e' he' => hsub e' (List.mem_cons_of_mem _ he')) _
      (fillInv_step h hc (hsub e List.mem_cons_self))

lemma fillInv_outer {cs : List TClaim} {kmax ntv : ℕ} :
    ∀ (cs' : List TClaim), (∀ c ∈ cs', c ∈ cs) → ∀ acc, FillInv cs kmax ntv acc →
      FillInv cs kmax ntv (cs'.foldl (fun acc (c : TClaim) => c.2.foldl (fun acc2 (e : CEntry) =>
        if e.1 ≤ kmax ∧ 1 ≤ c.1 ∧ c.1 ≤ ntv ∧ 0 < e.2.1 then
          acc2.modify e.1 (·.set! c.1 (some (logScaled true e.2.1 e.2.2.1, logScaled false e.2.2.2.1 e.2.2.2.2)))
        else acc2) acc) acc)
  | [], _, acc, h => h
  | c :: rest, hsub, acc, h => by
    rw [List.foldl_cons]
    exact fillInv_outer rest (fun c' hc' => hsub c' (List.mem_cons_of_mem _ hc')) _
      (fillInv_inner (hsub c List.mem_cons_self) c.2 (fun e he => he) acc h)

/-- The claim table: every `(k, j)` with `3 ≤ k ≤ kmax`, `1 ≤ j ≤ ntv` holds the log enclosures of a claim. -/
theorem claimLogs_spec {ntv kmax : ℕ} {cs : List TClaim} {L H : Array (Array ℤ)}
    (h : claimLogs ntv kmax cs = some (L, H)) :
    ∀ k, 3 ≤ k → k ≤ kmax → L[k]!.size = ntv + 1 ∧ H[k]!.size = ntv + 1 ∧
      ∀ j, 1 ≤ j → j ≤ ntv → ∃ c ∈ cs, ∃ e ∈ c.2, c.1 = j ∧ e.1 = k ∧ 0 < e.2.1 ∧
        (L[k]!)[j]! = logScaled true e.2.1 e.2.2.1 ∧ (H[k]!)[j]! = logScaled false e.2.2.2.1 e.2.2.2.2 := by
  unfold claimLogs at h
  set filled := cs.foldl (fun acc (c : TClaim) => c.2.foldl (fun acc2 (e : CEntry) =>
        if e.1 ≤ kmax ∧ 1 ≤ c.1 ∧ c.1 ≤ ntv ∧ 0 < e.2.1 then
          acc2.modify e.1 (·.set! c.1 (some (logScaled true e.2.1 e.2.2.1, logScaled false e.2.2.2.1 e.2.2.2.2)))
        else acc2) acc)
      (Array.replicate (kmax + 1) (Array.replicate (ntv + 1) (none : Option (ℤ × ℤ)))) with hfilled
  have hinv : FillInv cs kmax ntv filled := by
    apply fillInv_outer cs (fun c hc => hc)
    refine ⟨by simp, fun k hk => ?_, fun k j v hv => ?_⟩
    · rw [getElem!_pos _ k (by simpa using hk)]; simp
    · by_cases hk : k < kmax + 1
      · rw [getElem!_pos _ k (by simpa using hk)] at hv
        simp only [Array.getElem_replicate] at hv
        by_cases hj : j < ntv + 1
        · rw [getElem!_pos _ j (by simpa using hj)] at hv; simp at hv
        · rw [getElem!_neg _ j (by simpa using hj)] at hv; exact absurd hv (by simp [show (default : Option (ℤ × ℤ)) = none from rfl])
      · rw [getElem!_neg _ k (by simpa using hk), default_arr_getElem!] at hv; exact absurd hv (by simp)
  have hfold : (cs.foldl (fun acc (x : TClaim) => match x with
      | (j, lst) => lst.foldl (fun acc2 (y : CEntry) => match y with
        | (k, lm, le, hm, he) =>
          if k ≤ kmax ∧ 1 ≤ j ∧ j ≤ ntv ∧ 0 < lm then
            acc2.modify k (·.set! j (some (logScaled true lm le, logScaled false hm he)))
          else acc2) acc)
      (Array.replicate (kmax + 1) (Array.replicate (ntv + 1) (none : Option (ℤ × ℤ))))) = filled := rfl
  simp only [hfold] at h
  split_ifs at h with hok
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hL, hH⟩ := h
  simp only [List.all_eq_true, List.mem_range] at hok
  intro k hk3 hkm
  have hks : k < filled.size := by rw [hinv.size]; omega
  have hrow := hinv.rows k (by omega)
  have hLk : L[k]! = filled[k]!.map fun o => (o.getD (0, 0)).1 := by rw [← hL, getElem!_map _ _ hks]
  have hHk : H[k]! = filled[k]!.map fun o => (o.getD (0, 0)).2 := by rw [← hH, getElem!_map _ _ hks]
  refine ⟨by rw [hLk, Array.size_map, hrow], by rw [hHk, Array.size_map, hrow], fun j hj1 hj2 => ?_⟩
  have hsome := hok (k - 3) (by omega) (j - 1) (by omega)
  rw [show k - 3 + 3 = k by omega, show j - 1 + 1 = j by omega] at hsome
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨c, hc, e, he, hcj, hek, hlm, hve⟩ := hinv.ok k j v hv
  refine ⟨c, hc, e, he, hcj, hek, hlm, ?_, ?_⟩
  · rw [hLk, getElem!_map _ _ (by rw [hrow]; omega), hv, hve]; rfl
  · rw [hHk, getElem!_map _ _ (by rw [hrow]; omega), hv, hve]; rfl

/-! ## `tintOK` -/

lemma foldl_add_range_int (n : ℕ) (f : ℕ → ℤ) (a : ℤ) :
    (List.range n).foldl (fun acc k => acc + f k) a = a + ∑ k ∈ Finset.range n, f k := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]
    simp only [List.foldl_cons, List.foldl_nil]
    ring

theorem tintOK_spec {dtl T kmax lsub num den : ℕ} {cs : List TClaim} (h : tintOK dtl T kmax lsub cs num den = true) :
    ∃ L H, claimLogs (T * 2 ^ dtl) kmax cs = some (L, H) ∧
      (num : ℝ) / den ≤ ∑ k0 ∈ Finset.range (kmax - 5),
        fx (ckLo (k0 + 6) dtl (T * 2 ^ dtl) lsub L[k0 + 6]! H[k0 + 6]!
          (logTable (T * 2 ^ dtl * 2 ^ lsub) (dtl + lsub))) := by
  unfold tintOK at h
  dsimp only at h
  cases hcl : claimLogs (T * 2 ^ dtl) kmax cs with
  | none => rw [hcl] at h; simp at h
  | some LH =>
    obtain ⟨L, H⟩ := LH
    rw [hcl] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hden, hle⟩ := h
    refine ⟨L, H, rfl, ?_⟩
    rw [foldl_add_range_int, zero_add] at hle
    have hden' : (0 : ℝ) < den := by exact_mod_cast hden
    have hR : ((num : ℤ) : ℝ) * ((ONE : ℤ) : ℝ) ≤ ((∑ k0 ∈ Finset.range (kmax - 5),
        ckLo (k0 + 6) dtl (T * 2 ^ dtl) lsub L[k0 + 6]! H[k0 + 6]! (logTable (T * 2 ^ dtl * 2 ^ lsub) (dtl + lsub)) : ℤ) : ℝ) *
        (den : ℝ) := by exact_mod_cast hle
    have hONE : ((ONE : ℤ) : ℝ) = 2 ^ PR := by norm_num [ONE, PR]
    rw [hONE] at hR
    simp only [fx, ← Finset.sum_div]
    rw [div_le_div_iff₀ hden' (by positivity)]
    push_cast at hR
    linarith

/-! ## `Ψ^d` is a positive exponential sum -/

theorem isExpSum_psid (g : GridR) (hNR : 0 < g.NR) (hNT : 0 < g.NT) (D : DiscData) (m : ℕ)
    (hw : ∀ ir, 0 ≤ D.w ir) (hub : ∀ ir, 0 ≤ D.ub ir) (hab : ∀ ir ir2 d, 0 ≤ D.ab ir ir2 d) :
    IsExpSum (fun t => Psid g hNR hNT D m t) := by
  classical
  let e := Fintype.equivFin (CellSeq g m)
  refine ⟨Fintype.card (CellSeq g m),
    fun i => ((passVal2 (edgeA1 hNR hNT D (e.symm i)) (edgeA2 hNR hNT D (e.symm i)) (m + 1) : ℝ) / 2) *
      ∏ j, D.w ((e.symm i) j).1.val,
    fun i => expoSeq hNR hNT D (e.symm i), fun i => ?_, fun i => ?_, fun t => ?_⟩
  · apply mul_nonneg (by positivity)
    exact Finset.prod_nonneg fun j _ => hw _
  · unfold expoSeq
    exact add_nonneg (hub _) (Finset.sum_nonneg fun j _ => hab _ _ _)
  · show Psid g hNR hNT D m t = _
    unfold Psid
    refine Fintype.sum_equiv e _ _ (fun c => ?_)
    simp only [Equiv.symm_apply_apply]
    rw [mul_comm t]

end BHH.W2
