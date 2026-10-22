/-
Soundness of the table-based cos/sin `cosSinTab` (BHHCert/TrigTab.lean): `CosSinSound cosSinTab`.

The table entries are values of `cosSin` (sound by module A's `cosSin_sound`), the remainder angle is handled by
`NTT` Taylor terms with the remainder bound of `Complex.exp_bound` (module A's `taylorGo_spec`, `cos_sin_taylor`), and
the addition formulas `Real.cos_add`, `Real.sin_add` combine them.
-/
import BHH.Ivl.Trig
import BHHCert.TrigTab

open BHH.Cert

namespace BHH.E

/-- `sinCosTiny d` encloses `cos δ` and `sin δ`, `δ = d / 2^PR`, `|δ| ≤ 1` -/
lemma sinCosTiny_spec (d : ℤ) (hd : |(d : ℝ) / 2 ^ (PR + 0)| ≤ 1) :
    ivMem (Real.cos ((d : ℝ) / 2 ^ (PR + 0))) (sinCosTiny d).1 ∧
    ivMem (Real.sin ((d : ℝ) / 2 ^ (PR + 0))) (sinCosTiny d).2 := by
  have h0 : ivMem (((d : ℝ) / 2 ^ (PR + 0)) ^ 0 / (Nat.factorial 0 : ℝ)) (Iv.int 1) := by
    simpa using Iv.mem_int 1
  have hc0 : ivMem (cosPart 0 ((d : ℝ) / 2 ^ (PR + 0))) ⟨0, 0⟩ := by simp [cosPart, ivMem]
  have hs0 : ivMem (sinPart 0 ((d : ℝ) / 2 ^ (PR + 0))) ⟨0, 0⟩ := by simp [sinPart, ivMem]
  obtain ⟨hc, hsn, hlast⟩ :=
    taylorGo_spec d 0 NTT (NTT + 1) 0 (Iv.int 1) ⟨0, 0⟩ ⟨0, 0⟩ (by norm_num) (by norm_num) h0 hc0 hs0
  have hb := cos_sin_taylor ((d : ℝ) / 2 ^ (PR + 0)) hd NTT (by norm_num [NTT])
  generalize hres : taylorGo d 0 NTT (NTT + 1) 0 (Iv.int 1) ⟨0, 0⟩ ⟨0, 0⟩ = res at hc hsn hlast
  obtain ⟨c, sa, last⟩ := res
  simp only at hc hsn hlast
  generalize hsdef : (d : ℝ) / 2 ^ (PR + 0) = s at hc hsn hlast hb hd ⊢
  have hS := SC_pos
  have hmag := mag_bound hlast
  have hfac : (0 : ℝ) < (NTT.factorial : ℝ) := by positivity
  have hpow : |s ^ NTT / (NTT.factorial : ℝ)| = |s| ^ NTT / NTT.factorial := by
    rw [abs_div, abs_pow, abs_of_pos hfac]
  rw [hpow] at hmag
  generalize hmagdef : Max.max (Int.natAbs last.lo) (Int.natAbs last.hi) = mag at hmag
  have hN : (0 : ℝ) < NTT := by norm_num [NTT]
  have hrem : |s| ^ NTT * ((NTT.succ : ℝ) * (NTT.factorial * NTT : ℝ)⁻¹) * SC
      ≤ ((divU ((mag : ℤ) * (NTT + 1)) NTT + 1 : ℤ) : ℝ) := by
    have h2 := le_divU ((mag : ℤ) * (NTT + 1)) NTT (by norm_num [NTT])
    have e : |s| ^ NTT * ((NTT.succ : ℝ) * (NTT.factorial * NTT : ℝ)⁻¹) * SC
        = (|s| ^ NTT / NTT.factorial * SC) * ((NTT : ℝ) + 1) / NTT := by
      push_cast; field_simp
    rw [e]
    push_cast at h2 ⊢
    calc (|s| ^ NTT / NTT.factorial * SC) * ((NTT : ℝ) + 1) / NTT
        ≤ (mag : ℝ) * ((NTT : ℝ) + 1) / NTT := by gcongr
      _ ≤ _ := h2
      _ ≤ _ := by linarith
  have heq : sinCosTiny d = (Iv.widen c (divU ((mag : ℤ) * (NTT + 1)) NTT + 1),
      Iv.widen sa (divU ((mag : ℤ) * (NTT + 1)) NTT + 1)) := by
    unfold sinCosTiny
    rw [hres, ← hmagdef]
  rw [heq]
  exact ⟨mem_widen_of_approx hc.1 hc.2 hb.1 hrem, mem_widen_of_approx hsn.1 hsn.2 hb.2 hrem⟩

lemma mem_trivial_cos (x : ℝ) : ivMem (Real.cos x) (⟨-ONE, ONE⟩ : Iv) := by
  unfold ivMem; push_cast; rw [ONE_cast]
  have := Real.neg_one_le_cos x
  have := Real.cos_le_one x
  have hS := SC_pos
  constructor <;> nlinarith

lemma mem_trivial_sin (x : ℝ) : ivMem (Real.sin x) (⟨-ONE, ONE⟩ : Iv) := by
  unfold ivMem; push_cast; rw [ONE_cast]
  have := Real.neg_one_le_sin x
  have := Real.sin_le_one x
  have hS := SC_pos
  constructor <;> nlinarith

lemma getD_map_range_lt {α : Type*} (f : ℕ → α) (n j : ℕ) (d : α) (hj : j < n) :
    ((List.range n).map f).toArray.getD j d = f j := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map, List.getElem?_range hj]
  rfl

lemma getD_map_range_ge {α : Type*} (f : ℕ → α) (n j : ℕ) (d : α) (hj : ¬ j < n) :
    ((List.range n).map f).toArray.getD j d = d := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_eq_none (by rw [List.length_range]; omega)]
  rfl

lemma csTable_getD_lt (j : ℕ) (hj : j < 7 * 2 ^ TB + 1) :
    csTable.getD j csTrivial = cosSin ((j : ℤ) * 2 ^ (PR - TB)) :=
  getD_map_range_lt (fun j : ℕ => cosSin ((j : ℤ) * 2 ^ (PR - TB))) _ j csTrivial hj

lemma csTable_getD_ge (j : ℕ) (hj : ¬ j < 7 * 2 ^ TB + 1) : csTable.getD j csTrivial = csTrivial :=
  getD_map_range_ge (fun j : ℕ => cosSin ((j : ℤ) * 2 ^ (PR - TB))) _ j csTrivial hj

/-- every table entry encloses `cos` and `sin` of its grid point, or is trivial -/
lemma csTable_entry (j : ℕ) (hj : j * 2 ^ (PR - TB) ≤ 7 * ONE.toNat) :
    ivMem (Real.cos (fx ((j : ℤ) * 2 ^ (PR - TB)))) (csTable.getD j csTrivial).1 ∧
    ivMem (Real.sin (fx ((j : ℤ) * 2 ^ (PR - TB)))) (csTable.getD j csTrivial).2 := by
  by_cases hjs : j < 7 * 2 ^ TB + 1
  · rw [csTable_getD_lt j hjs]
    apply cosSin_sound
    have : ((j : ℤ) * 2 ^ (PR - TB)).natAbs = j * 2 ^ (PR - TB) := by
      rw [Int.natAbs_mul]; simp
    rw [this]; exact hj
  · rw [csTable_getD_ge j hjs]
    exact ⟨mem_trivial_cos _, mem_trivial_sin _⟩

theorem cosSinTab_sound : CosSinSound cosSinTab := by
  intro t ht
  unfold cosSinTab
  rw [ite_eq_left ht]
  simp only
  set a := t.natAbs with ha
  set j := a >>> (PR - TB) with hjdef
  set d : ℤ := (a : ℤ) - (j : ℤ) * 2 ^ (PR - TB) with hd
  have hjdiv : j = a / 2 ^ (PR - TB) := by rw [hjdef, Nat.shiftRight_eq_div_pow]
  have hP : 0 < 2 ^ (PR - TB) := by positivity
  have hja : j * 2 ^ (PR - TB) ≤ a := by rw [hjdiv]; exact Nat.div_mul_le_self a _
  have hmod : (a : ℤ) = (j : ℤ) * 2 ^ (PR - TB) + ((a % 2 ^ (PR - TB) : ℕ) : ℤ) := by
    have h := Nat.div_add_mod a (2 ^ (PR - TB))
    rw [hjdiv]
    have h' : ((2 ^ (PR - TB) * (a / 2 ^ (PR - TB)) + a % 2 ^ (PR - TB) : ℕ) : ℤ) = (a : ℤ) := by
      exact_mod_cast h
    push_cast at h' ⊢
    linarith
  have hd' : d = ((a % 2 ^ (PR - TB) : ℕ) : ℤ) := by rw [hd]; linarith [hmod]
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := by rw [hd']; positivity
  have hd1 : (d : ℝ) < 2 ^ (PR - TB) := by
    rw [hd']
    have := Nat.mod_lt a hP
    exact_mod_cast this
  have hent := csTable_entry j (le_trans hja ht)
  have hδ : |(d : ℝ) / 2 ^ (PR + 0)| ≤ 1 := by
    rw [abs_of_nonneg (by positivity), div_le_one (by positivity)]
    have h1 : (2 : ℝ) ^ (PR - TB) ≤ 2 ^ (PR + 0) := pow_le_pow_right₀ (by norm_num) (by simp [PR, TB])
    linarith
  have htiny := sinCosTiny_spec d hδ
  have hsum : fx ((j : ℤ) * 2 ^ (PR - TB)) + (d : ℝ) / 2 ^ (PR + 0) = fx (a : ℤ) := by
    simp only [fx, add_zero]
    rw [hd]
    push_cast
    field_simp
    ring
  have hc := Iv.mem_sub (Iv.mem_mul hent.1 htiny.1) (Iv.mem_mul hent.2 htiny.2)
  have hs := Iv.mem_add (Iv.mem_mul hent.2 htiny.1) (Iv.mem_mul hent.1 htiny.2)
  rw [← Real.cos_add, hsum] at hc
  rw [show Real.sin (fx ((j : ℤ) * 2 ^ (PR - TB))) * Real.cos ((d : ℝ) / 2 ^ (PR + 0)) +
      Real.cos (fx ((j : ℤ) * 2 ^ (PR - TB))) * Real.sin ((d : ℝ) / 2 ^ (PR + 0)) =
      Real.sin (fx ((j : ℤ) * 2 ^ (PR - TB)) + (d : ℝ) / 2 ^ (PR + 0)) by rw [Real.sin_add], hsum] at hs
  have habs : ((a : ℕ) : ℤ) = |t| := by rw [ha, Int.natCast_natAbs]
  by_cases h0 : t < 0
  · rw [ite_eq_left h0]
    have e : fx t = -fx (a : ℤ) := by
      rw [habs, abs_of_neg h0]; simp [fx, neg_div]
    rw [e, Real.cos_neg]
    have hs' := Iv.mem_neg hs
    rw [← Real.sin_neg] at hs'
    exact ⟨clip1_cos hc, clip1_sin hs'⟩
  · rw [ite_eq_right h0]
    have e : fx t = fx (a : ℤ) := by
      rw [habs, abs_of_nonneg (not_lt.mp h0)]
    rw [e]
    exact ⟨clip1_cos hc, clip1_sin hs⟩

end BHH.E

namespace BHH

-- the deliverable of this file, also under `BHH` (helpers stay in `BHH.E`)
export E (cosSinTab_sound)

end BHH
