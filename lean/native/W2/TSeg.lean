/-
Module T: soundness of `W2C.xLo` and `W2C.segLo` (W2Cert/TInt.lean):
`segLo k α γ ja dtl lsub logs ≤ ∫_{ja 2^-dtl}^{(ja+1) 2^-dtl} t^{k-3/2} e^{α - γ t} dt` (fixed point, in `[0, ∞]`).
-/
import W2.FixSound
import W2.TSub
import W2.Interfaces

open MeasureTheory Set Real BHH.Cert
open scoped ENNReal

noncomputable section

namespace BHH.W2

open BHH

/-! ## Fixed-point helpers -/

lemma tfx_add (a b : ℤ) : fx (a + b) = fx a + fx b := by simp only [fx_eq]; push_cast; ring

lemma tfx_sub (a b : ℤ) : fx (a - b) = fx a - fx b := by simp only [fx_eq]; push_cast; ring

lemma tfx_zero : fx 0 = 0 := by simp [fx_eq]

lemma tfx_ONE : fx ONE = 1 := by rw [fx_eq, ONE_cast]; exact div_self SC_pos.ne'

lemma tfx_max (a b : ℤ) : fx (max a b) = max (fx a) (fx b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (fx_le_iff.2 h)]
  · rw [max_eq_left h, max_eq_left (fx_le_iff.2 h)]

lemma tfx_shrD_le (a : ℤ) (n : ℕ) : fx (shrD a n) ≤ fx a / 2 ^ n := by
  have h := shrD_le a n
  rw [fx_eq, fx_eq, div_right_comm]
  exact div_le_div_of_nonneg_right h SC_pos.le

lemma tfx_divD_le (a b : ℤ) (hb : 0 < b) : fx (divD a b) ≤ fx a / b := by
  have h := divD_le a b hb
  rw [fx_eq, fx_eq, div_right_comm]
  exact div_le_div_of_nonneg_right h SC_pos.le

lemma le_tfx_divU (a b : ℤ) (hb : 0 < b) : fx a / b ≤ fx (divU a b) := by
  have h := le_divU a b hb
  rw [fx_eq, fx_eq, div_right_comm]
  exact div_le_div_of_nonneg_right h SC_pos.le

lemma tfx_shrD_mul_le (a b : ℤ) : fx (shrD (a * b) PR) ≤ fx a * fx b := by
  have h := shrD_le (a * b) PR
  rw [fx_eq, fx_eq, fx_eq]
  calc ((shrD (a * b) PR : ℤ) : ℝ) / SC ≤ (((a * b : ℤ) : ℝ) / 2 ^ PR) / SC :=
        div_le_div_of_nonneg_right h SC_pos.le
    _ = (a : ℝ) / SC * ((b : ℝ) / SC) := by push_cast; simp only [SC]; field_simp

/-! ## `xLo` -/

lemma xLo_spec (k : ℕ) (hk : 2 ≤ k) (alpha gamma logt : ℤ) (m q : ℕ)
    (hlog : fx logt ≤ Real.log ((m : ℝ) / 2 ^ q)) :
    fx (W2C.xLo k alpha gamma logt m q) ≤
      ((k : ℝ) - 3 / 2) * Real.log ((m : ℝ) / 2 ^ q) + fx alpha - fx gamma * ((m : ℝ) / 2 ^ q) := by
  have hSC := SC_pos
  have hgt : fx gamma * ((m : ℝ) / 2 ^ q) ≤ fx (divU (gamma * (m : ℤ)) (2 ^ q)) := by
    have h := le_divU (gamma * (m : ℤ)) (2 ^ q) (by positivity)
    push_cast at h
    have e : fx gamma * ((m : ℝ) / 2 ^ q) = ((gamma : ℝ) * (m : ℝ) / 2 ^ q) / SC := by rw [fx_eq]; ring
    rw [e, fx_eq]
    exact div_le_div_of_nonneg_right h hSC.le
  have hd : fx (divD ((2 * (k : ℤ) - 3) * logt) 2) ≤ ((k : ℝ) - 3 / 2) * Real.log ((m : ℝ) / 2 ^ q) := by
    have h := divD_le ((2 * (k : ℤ) - 3) * logt) 2 (by norm_num)
    push_cast at h
    have hk' : (0 : ℝ) ≤ (k : ℝ) - 3 / 2 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    calc fx (divD ((2 * (k : ℤ) - 3) * logt) 2) = ((divD ((2 * (k : ℤ) - 3) * logt) 2 : ℤ) : ℝ) / SC := fx_eq _
      _ ≤ ((2 * (k : ℝ) - 3) * (logt : ℝ) / 2) / SC := div_le_div_of_nonneg_right h hSC.le
      _ = ((k : ℝ) - 3 / 2) * fx logt := by rw [fx_eq]; ring
      _ ≤ ((k : ℝ) - 3 / 2) * Real.log ((m : ℝ) / 2 ^ q) := mul_le_mul_of_nonneg_left hlog hk'
  unfold W2C.xLo
  rw [tfx_add, tfx_sub]
  linarith

/-! ## One term of the sum -/

/-- one term of the `segLo` sum (sub-interval `[i w, (i+1) w]`, `X = fx xa`, `Y = fx xb`) -/
def segTerm (k : ℕ) (xa xb : ℤ) (i : ℕ) : ℤ :=
  shrD (Max.max (W2C.expPt (divD (xa + xb) 2)).lo 0 *
    Max.max (ONE + divD (shrD ((xb - xa) * (xb - xa)) PR) 24 +
      divD ((2 * (k : Int) - 3) * ONE) (24 * ((i + 1) * (i + 1) : Nat))) 0) PR

lemma segTerm_spec (k : ℕ) (hk : 2 ≤ k) (xa xb : ℤ) (i : ℕ) :
    fx (segTerm k xa xb i) ≤ Real.exp ((fx xa + fx xb) / 2) *
      (1 + (fx xb - fx xa) ^ 2 / 24 + ((k : ℝ) - 3 / 2) / (12 * ((i : ℝ) + 1) ^ 2)) := by
  unfold segTerm
  set M := divD (xa + xb) 2 with hMdef
  set eM := Max.max (W2C.expPt M).lo 0 with heMdef
  set fac := ONE + divD (shrD ((xb - xa) * (xb - xa)) PR) 24 +
    divD ((2 * (k : Int) - 3) * ONE) (24 * ((i + 1) * (i + 1) : Nat)) with hfacdef
  have h1 := tfx_shrD_mul_le eM (Max.max fac 0)
  have heM0 : 0 ≤ fx eM := by rw [heMdef, tfx_max, tfx_zero]; exact le_max_right _ _
  have hM : fx M ≤ (fx xa + fx xb) / 2 := by
    have := tfx_divD_le (xa + xb) 2 (by norm_num)
    rw [tfx_add] at this
    push_cast at this
    exact this
  have heM : fx eM ≤ Real.exp ((fx xa + fx xb) / 2) := by
    rw [heMdef, tfx_max, tfx_zero]
    exact max_le ((expPt_lo M).trans (Real.exp_le_exp.2 hM)) (Real.exp_pos _).le
  have hk' : (0 : ℝ) ≤ (k : ℝ) - 3 / 2 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hR : 0 ≤ 1 + (fx xb - fx xa) ^ 2 / 24 + ((k : ℝ) - 3 / 2) / (12 * ((i : ℝ) + 1) ^ 2) := by positivity
  have hfac : fx fac ≤ 1 + (fx xb - fx xa) ^ 2 / 24 + ((k : ℝ) - 3 / 2) / (12 * ((i : ℝ) + 1) ^ 2) := by
    have hD2 := tfx_shrD_mul_le (xb - xa) (xb - xa)
    have hd1 := tfx_divD_le (shrD ((xb - xa) * (xb - xa)) PR) 24 (by norm_num)
    have hd2 := tfx_divD_le ((2 * (k : Int) - 3) * ONE) (24 * ((i + 1) * (i + 1) : Nat)) (by positivity)
    have e2 : fx ((2 * (k : Int) - 3) * ONE) = 2 * (k : ℝ) - 3 := by
      rw [fx_eq]; push_cast; rw [ONE_cast]; field_simp
    rw [e2] at hd2
    rw [tfx_sub] at hD2
    push_cast at hd1
    rw [show ((24 * ((i + 1) * (i + 1) : ℕ) : ℤ) : ℝ) = 24 * (((i : ℝ) + 1) * ((i : ℝ) + 1)) by push_cast; ring]
      at hd2
    have e3 : (2 * (k : ℝ) - 3) / (24 * (((i : ℝ) + 1) * ((i : ℝ) + 1))) =
        ((k : ℝ) - 3 / 2) / (12 * ((i : ℝ) + 1) ^ 2) := by
      field_simp; ring
    rw [e3] at hd2
    rw [hfacdef, tfx_add, tfx_add, tfx_ONE]
    have h24 : fx (shrD ((xb - xa) * (xb - xa)) PR) / 24 ≤ (fx xb - fx xa) ^ 2 / 24 := by
      have := div_le_div_of_nonneg_right hD2 (by norm_num : (0 : ℝ) ≤ 24)
      nlinarith [this]
    linarith
  have hmax : fx (Max.max fac 0) ≤ 1 + (fx xb - fx xa) ^ 2 / 24 + ((k : ℝ) - 3 / 2) / (12 * ((i : ℝ) + 1) ^ 2) := by
    rw [tfx_max, tfx_zero]; exact max_le hfac hR
  have hmax0 : 0 ≤ fx (Max.max fac 0) := by rw [tfx_max, tfx_zero]; exact le_max_right _ _
  calc fx (shrD (eM * Max.max fac 0) PR) ≤ fx eM * fx (Max.max fac 0) := h1
    _ ≤ _ := mul_le_mul heM hmax hmax0 (Real.exp_pos _).le

/-! ## The loop of `segLo` -/

/-- the loop body of `W2C.segLo` -/
def segStep (k : ℕ) (alpha gamma : ℤ) (q i0 : ℕ) (logs : Array ℤ) (st : ℤ × ℤ) (m : ℕ) : ℤ × ℤ :=
  let (xa, acc) := st
  let i := i0 + m
  let xb := W2C.xLo k alpha gamma logs[i + 1]! (i + 1) q
  if i == 0 then (xb, acc) else
  let M := divD (xa + xb) 2
  let eM := Max.max (W2C.expPt M).lo 0
  let D := xb - xa
  let D2 := shrD (D * D) PR
  let f1 : Int := ONE + divD D2 24
  let kap : Int := divD ((2 * (k : Int) - 3) * ONE) (24 * ((i + 1) * (i + 1) : Nat))
  let fac : Int := f1 + kap
  let term := shrD (eM * Max.max fac 0) PR
  (xb, acc + term)

lemma segLo_eq (k : ℕ) (alpha gamma : ℤ) (ja dtl lsub : ℕ) (logs : Array ℤ) :
    W2C.segLo k alpha gamma ja dtl lsub logs =
      shrD ((List.range (2 ^ lsub)).foldl (segStep k alpha gamma (dtl + lsub) (ja * 2 ^ lsub) logs)
        (W2C.xLo k alpha gamma logs[ja * 2 ^ lsub]! (ja * 2 ^ lsub) (dtl + lsub), 0)).2 (dtl + lsub) := rfl

lemma segStep_fst (k : ℕ) (alpha gamma : ℤ) (q i0 : ℕ) (logs : Array ℤ) (st : ℤ × ℤ) (m : ℕ) :
    (segStep k alpha gamma q i0 logs st m).1 = W2C.xLo k alpha gamma logs[i0 + m + 1]! (i0 + m + 1) q := by
  obtain ⟨xa, acc⟩ := st
  unfold segStep
  dsimp only
  split_ifs <;> rfl

lemma segStep_snd_zero (k : ℕ) (alpha gamma : ℤ) (q i0 : ℕ) (logs : Array ℤ) (st : ℤ × ℤ) (m : ℕ)
    (h : i0 + m = 0) : (segStep k alpha gamma q i0 logs st m).2 = st.2 := by
  obtain ⟨xa, acc⟩ := st
  unfold segStep
  simp [h]

lemma segStep_snd (k : ℕ) (alpha gamma : ℤ) (q i0 : ℕ) (logs : Array ℤ) (st : ℤ × ℤ) (m : ℕ)
    (h : i0 + m ≠ 0) : (segStep k alpha gamma q i0 logs st m).2 =
      st.2 + segTerm k st.1 (W2C.xLo k alpha gamma logs[i0 + m + 1]! (i0 + m + 1) q) (i0 + m) := by
  obtain ⟨xa, acc⟩ := st
  have hb : (i0 + m == 0) = false := by simpa using h
  unfold segStep
  simp only [hb, Bool.false_eq_true, ↓reduceIte]
  rfl

lemma foldl_range_succ {α : Type*} (F : α → ℕ → α) (init : α) (m : ℕ) :
    (List.range (m + 1)).foldl F init = F ((List.range m).foldl F init) m := by
  rw [List.range_succ, List.foldl_append]; rfl

lemma ofReal_intervalIntegral_eq {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hg : Continuous g)
    (hg0 : ∀ t ∈ Ioc a b, 0 ≤ g t) :
    ENNReal.ofReal (∫ t in a..b, g t) = ∫⁻ t in Ioc a b, ENNReal.ofReal (g t) := by
  rw [intervalIntegral.integral_of_le hab]
  exact ofReal_integral_eq_lintegral_ofReal hg.integrableOn_Ioc
    ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall hg0))

/-- soundness of `segLo` -/
theorem segLo_spec (k : ℕ) (hk : 2 ≤ k) (alpha gamma : ℤ) (ja dtl lsub : ℕ) (logs : Array ℤ)
    (hlogs : ∀ i, 1 ≤ i → i ≤ (ja + 1) * 2 ^ lsub → fx logs[i]! ≤ Real.log ((i : ℝ) / 2 ^ (dtl + lsub))) :
    ENNReal.ofReal (fx (W2C.segLo k alpha gamma ja dtl lsub logs)) ≤
      ∫⁻ t in Ioc ((ja : ℝ) / 2 ^ dtl) (((ja : ℝ) + 1) / 2 ^ dtl),
        ENNReal.ofReal (t ^ ((k : ℝ) - 3 / 2) * Real.exp (fx alpha - fx gamma * t)) := by
  rw [segLo_eq]
  set n := 2 ^ lsub with hn
  set q := dtl + lsub with hq
  set i0 := ja * 2 ^ lsub with hi0
  have hn' : i0 + n = (ja + 1) * 2 ^ lsub := by rw [hi0, hn]; ring
  have hlogs' : ∀ i, 1 ≤ i → i ≤ i0 + n → fx logs[i]! ≤ Real.log ((i : ℝ) / 2 ^ q) := by
    intro i h1 h2; exact hlogs i h1 (hn' ▸ h2)
  have hc : (0 : ℝ) ≤ (k : ℝ) - 3 / 2 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  set g : ℝ → ℝ := fun t => t ^ ((k : ℝ) - 3 / 2) * Real.exp (fx alpha - fx gamma * t) with hg
  have hgc : Continuous g := (Real.continuous_rpow_const hc).mul (by fun_prop)
  have hq0 : (0 : ℝ) < 2 ^ q := by positivity
  -- the sub-interval bound, in `[0, ∞]`
  have hsub : ∀ i : ℕ, 1 ≤ i → ∀ xa xb : ℤ,
      fx xa ≤ ((k : ℝ) - 3 / 2) * Real.log ((i : ℝ) / 2 ^ q) + fx alpha - fx gamma * ((i : ℝ) / 2 ^ q) →
      fx xb ≤ ((k : ℝ) - 3 / 2) * Real.log (((i + 1 : ℕ) : ℝ) / 2 ^ q) + fx alpha -
        fx gamma * (((i + 1 : ℕ) : ℝ) / 2 ^ q) →
      ENNReal.ofReal (fx (segTerm k xa xb i) / 2 ^ q) ≤
        ∫⁻ t in Ioc ((i : ℝ) / 2 ^ q) (((i + 1 : ℕ) : ℝ) / 2 ^ q), ENNReal.ofReal (g t) := by
    intro i hi xa xb hX hY
    have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
    have ha : (0 : ℝ) < (i : ℝ) / 2 ^ q := by positivity
    have hab : (i : ℝ) / 2 ^ q < ((i + 1 : ℕ) : ℝ) / 2 ^ q := by
      push_cast; exact div_lt_div_of_pos_right (by linarith) hq0
    have hsb := sub_bound ha hab hc hX hY
    rw [← ofReal_intervalIntegral_eq hab.le hgc (fun t ht => mul_nonneg
      (Real.rpow_nonneg (ha.trans ht.1).le _) (Real.exp_pos _).le)]
    apply ENNReal.ofReal_le_ofReal
    refine le_trans ?_ hsb
    have ht := segTerm_spec k hk xa xb i
    have hw : ((i + 1 : ℕ) : ℝ) / 2 ^ q - (i : ℝ) / 2 ^ q = 1 / 2 ^ q := by push_cast; ring
    have hκ : ((k : ℝ) - 3 / 2) * (1 / 2 ^ q) ^ 2 / (12 * (((i + 1 : ℕ) : ℝ) / 2 ^ q) ^ 2) =
        ((k : ℝ) - 3 / 2) / (12 * ((i : ℝ) + 1) ^ 2) := by
      push_cast; field_simp
    rw [hw, hκ]
    calc fx (segTerm k xa xb i) / 2 ^ q = 1 / 2 ^ q * fx (segTerm k xa xb i) := by ring
      _ ≤ 1 / 2 ^ q * (Real.exp ((fx xa + fx xb) / 2) *
          (1 + (fx xb - fx xa) ^ 2 / 24 + ((k : ℝ) - 3 / 2) / (12 * ((i : ℝ) + 1) ^ 2))) :=
          mul_le_mul_of_nonneg_left ht (by positivity)
      _ = _ := by ring
  -- the loop invariant
  have hinv : ∀ m, m ≤ n →
      ((List.range m).foldl (segStep k alpha gamma q i0 logs) (W2C.xLo k alpha gamma logs[i0]! i0 q, 0)).1 =
        W2C.xLo k alpha gamma logs[i0 + m]! (i0 + m) q ∧
      ENNReal.ofReal (fx ((List.range m).foldl (segStep k alpha gamma q i0 logs)
          (W2C.xLo k alpha gamma logs[i0]! i0 q, 0)).2 / 2 ^ q) ≤
        ∫⁻ t in Ioc ((i0 : ℝ) / 2 ^ q) (((i0 + m : ℕ) : ℝ) / 2 ^ q), ENNReal.ofReal (g t) := by
    intro m
    induction m with
    | zero => intro _; simp [tfx_zero]
    | succ m ih =>
      intro hm
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      rw [foldl_range_succ, ← Nat.add_assoc]
      refine ⟨segStep_fst _ _ _ _ _ _ _ _, ?_⟩
      have hle : ((i0 + m : ℕ) : ℝ) / 2 ^ q ≤ ((i0 + m + 1 : ℕ) : ℝ) / 2 ^ q := by
        push_cast; exact div_le_div_of_nonneg_right (by linarith) hq0.le
      have hle0 : (i0 : ℝ) / 2 ^ q ≤ ((i0 + m : ℕ) : ℝ) / 2 ^ q := by
        push_cast; exact div_le_div_of_nonneg_right (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]) hq0.le
      by_cases h0 : i0 + m = 0
      · rw [segStep_snd_zero _ _ _ _ _ _ _ _ h0]
        exact ih2.trans (lintegral_mono_set (Ioc_subset_Ioc le_rfl hle))
      · rw [segStep_snd _ _ _ _ _ _ _ _ h0, tfx_add, add_div]
        refine ENNReal.ofReal_add_le.trans ?_
        have hX := xLo_spec k hk alpha gamma logs[i0 + m]! (i0 + m) q (hlogs' _ (by omega) (by omega))
        rw [← ih1] at hX
        have hY := xLo_spec k hk alpha gamma logs[i0 + m + 1]! (i0 + m + 1) q (hlogs' _ (by omega) (by omega))
        have hT := hsub (i0 + m) (by omega) _ _ hX hY
        calc _ ≤ (∫⁻ t in Ioc ((i0 : ℝ) / 2 ^ q) (((i0 + m : ℕ) : ℝ) / 2 ^ q), ENNReal.ofReal (g t)) +
              ∫⁻ t in Ioc (((i0 + m : ℕ) : ℝ) / 2 ^ q) (((i0 + m + 1 : ℕ) : ℝ) / 2 ^ q), ENNReal.ofReal (g t) :=
            add_le_add ih2 hT
          _ = _ := by
            rw [← lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl), Ioc_union_Ioc_eq_Ioc hle0 hle]
  obtain ⟨_, hfin⟩ := hinv n le_rfl
  have he1 : (i0 : ℝ) / 2 ^ q = (ja : ℝ) / 2 ^ dtl := by
    rw [hi0, hq]; push_cast; rw [pow_add]; field_simp
  have he2 : ((i0 + n : ℕ) : ℝ) / 2 ^ q = ((ja : ℝ) + 1) / 2 ^ dtl := by
    rw [hn', hq]; push_cast; rw [pow_add]; field_simp
  rw [he1, he2] at hfin
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hfin
  exact tfx_shrD_le _ _

end BHH.W2
