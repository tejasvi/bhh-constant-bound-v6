/-
Module T: `TIntBound`, the soundness of `W2C.ckLo` (paper Section 4.4): on `[0, t_1]` the value at
`t_1`, on `[t_j, t_{j+1}]` the best of the value at `t_{j+1}` and the left and right extended secants (log-convexity
of the exponential sum), each integrated by `segLo` (`segLo_spec`), summed over the segments and halved.
-/
import W2.TSeg
import W2.TExpSum

open MeasureTheory Set Real BHH.Cert
open scoped ENNReal

noncomputable section

namespace BHH.W2

open BHH

/-- the left extended secant piece of `W2C.ckLo` on segment `j` -/
def segC2 (k dtl lsub : ℕ) (L H logs : Array ℤ) (j : ℕ) : ℤ :=
  if 2 ≤ j then
    let sig : Int := (L[j]! - H[j - 1]!) * 2 ^ dtl
    if sig < piLo then
      let alpha := L[j]! - divU (sig * j) (2 ^ dtl)
      W2C.segLo k alpha (piHi - sig) j dtl lsub logs
    else 0
  else 0

/-- the right extended secant piece of `W2C.ckLo` on segment `j` -/
def segC3 (k dtl ntv lsub : ℕ) (L H logs : Array ℤ) (j : ℕ) : ℤ :=
  if j + 2 ≤ ntv then
    let sig : Int := (H[j + 2]! - L[j + 1]!) * 2 ^ dtl
    if sig < piLo then
      let alpha := L[j + 1]! - divU (sig * (j + 1)) (2 ^ dtl)
      W2C.segLo k alpha (piHi - sig) j dtl lsub logs
    else 0
  else 0

/-- the best of the three pieces of `W2C.ckLo` on segment `j` -/
def segBest (k dtl ntv lsub : ℕ) (L H logs : Array ℤ) (j : ℕ) : ℤ :=
  Max.max (W2C.segLo k L[j + 1]! piHi j dtl lsub logs) (Max.max (segC2 k dtl lsub L H logs j) (segC3 k dtl ntv lsub L H logs j))

lemma ckLo_eq (k dtl ntv lsub : ℕ) (L H logs : Array ℤ) :
    W2C.ckLo k dtl ntv lsub L H logs =
      shrD ((List.range (ntv - 1)).foldl (fun acc j0 => acc + segBest k dtl ntv lsub L H logs (j0 + 1))
        (W2C.segLo k L[1]! piHi 0 dtl lsub logs)) 1 := rfl

theorem tIntBound : TIntBound := by
  intro k dtl ntv lsub f L H logs hk hntv hf hLs hHs hlogsz hLH hlogs
  have hk2 : 2 ≤ k := by omega
  have hpos : ∀ t, 0 < f t := expSum_pos hf (hLH 1 le_rfl (by omega)).1
  have hanti := expSum_anti hf
  have hconv := expSum_logConvex hf hpos
  have hdt : (0 : ℝ) < 2 ^ dtl := by positivity
  set F : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ ((k : ℝ) - 3 / 2) * Real.exp (-(π * t))) *
    ENNReal.ofReal (f t) with hF
  -- one segment, for any affine minorant
  have hseg : ∀ (j : ℕ) (alpha gamma : ℤ) (σ : ℝ), j + 1 ≤ ntv → π - σ ≤ fx gamma →
      (∀ t ∈ Ioc ((j : ℝ) / 2 ^ dtl) (((j : ℝ) + 1) / 2 ^ dtl), fx alpha + σ * t ≤ Real.log (f t)) →
      ENNReal.ofReal (fx (W2C.segLo k alpha gamma j dtl lsub logs)) ≤
        ∫⁻ t in Ioc ((j : ℝ) / 2 ^ dtl) (((j : ℝ) + 1) / 2 ^ dtl), F t := by
    intro j alpha gamma σ hj hγ hmin
    refine (segLo_spec k hk2 alpha gamma j dtl lsub logs ?_).trans ?_
    · intro i hi1 hi2
      exact hlogs i hi1 (le_trans hi2 (Nat.mul_le_mul_right _ hj))
    · refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
      have ht0 : 0 ≤ t := le_trans (by positivity) ht.1.le
      simp only [hF]
      rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg ht0 _) (Real.exp_pos _).le)]
      exact ENNReal.ofReal_le_ofReal (minorant_integrand ht0 (hpos t) (hmin t ht) hγ)
  -- the value minorant: `log f(t) ≥ L[j]` for `t ≤ t_j`
  have hval : ∀ j, 1 ≤ j → j ≤ ntv → ∀ t, t ≤ (j : ℝ) / 2 ^ dtl → fx L[j]! ≤ Real.log (f t) := by
    intro j h1 h2 t ht
    obtain ⟨hp, hl, _⟩ := hLH j h1 h2
    exact hl.trans (Real.log_le_log hp (hanti ht))
  have hpi : π - 0 ≤ fx piHi := by rw [sub_zero]; exact le_piHi
  -- the three pieces on segment `j`
  have hbest : ∀ j, 1 ≤ j → j + 1 ≤ ntv → ENNReal.ofReal (fx (segBest k dtl ntv lsub L H logs j)) ≤
      ∫⁻ t in Ioc ((j : ℝ) / 2 ^ dtl) (((j : ℝ) + 1) / 2 ^ dtl), F t := by
    intro j hj1 hj2
    have h1 : ENNReal.ofReal (fx (W2C.segLo k L[j + 1]! piHi j dtl lsub logs)) ≤
        ∫⁻ t in Ioc ((j : ℝ) / 2 ^ dtl) (((j : ℝ) + 1) / 2 ^ dtl), F t := by
      refine hseg j _ _ 0 hj2 hpi fun t ht => ?_
      rw [zero_mul, add_zero]
      exact hval (j + 1) (by omega) hj2 t (by push_cast; exact ht.2)
    have h2 : ENNReal.ofReal (fx (segC2 k dtl lsub L H logs j)) ≤
        ∫⁻ t in Ioc ((j : ℝ) / 2 ^ dtl) (((j : ℝ) + 1) / 2 ^ dtl), F t := by
      unfold segC2
      dsimp only
      split_ifs with h2j hsig
      · set sig : ℤ := (L[j]! - H[j - 1]!) * 2 ^ dtl with hsigdef
        refine hseg j _ _ (fx sig) hj2 (by rw [tfx_sub]; linarith [le_piHi]) fun t ht => ?_
        set x : ℝ := ((j - 1 : ℕ) : ℝ) / 2 ^ dtl with hx
        set y : ℝ := (j : ℝ) / 2 ^ dtl with hy
        have hj1' : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
        have hyx : y - x = 1 / 2 ^ dtl := by rw [hx, hy, hj1']; field_simp; ring
        have hxy : x < y := by rw [← sub_pos, hyx]; positivity
        have hyt : y ≤ t := ht.1.le
        have hsec : Real.log (f y) + (Real.log (f y) - Real.log (f x)) / (y - x) * (t - y) ≤ Real.log (f t) :=
          secant_right hconv hxy hyt
        have hLy : fx L[j]! ≤ Real.log (f y) := (hLH j hj1 (by omega)).2.1
        have hHx : Real.log (f x) ≤ fx H[j - 1]! := (hLH (j - 1) (by omega) (by omega)).2.2
        have hfsig : fx sig = (fx L[j]! - fx H[j - 1]!) * 2 ^ dtl := by
          rw [hsigdef, fx_eq, fx_eq, fx_eq]; push_cast; ring
        have hslope : fx sig ≤ (Real.log (f y) - Real.log (f x)) / (y - x) := by
          rw [le_div_iff₀ (sub_pos.2 hxy), hyx, hfsig]
          have e : (fx L[j]! - fx H[j - 1]!) * 2 ^ dtl * (1 / 2 ^ dtl) = fx L[j]! - fx H[j - 1]! := by field_simp
          rw [e]; linarith
        have hm := mul_le_mul_of_nonneg_right hslope (sub_nonneg.2 hyt)
        have hdiv := le_tfx_divU (sig * (j : ℤ)) (2 ^ dtl) (by positivity)
        have e1 : fx (sig * (j : ℤ)) / ((2 ^ dtl : ℤ) : ℝ) = fx sig * y := by
          rw [hy, fx_eq, fx_eq]; push_cast; ring
        rw [e1] at hdiv
        rw [tfx_sub]
        nlinarith [hm, hdiv, hsec, hLy]
      · simp [tfx_zero]
      · simp [tfx_zero]
    have h3 : ENNReal.ofReal (fx (segC3 k dtl ntv lsub L H logs j)) ≤
        ∫⁻ t in Ioc ((j : ℝ) / 2 ^ dtl) (((j : ℝ) + 1) / 2 ^ dtl), F t := by
      unfold segC3
      dsimp only
      split_ifs with h2j hsig
      · set sig : ℤ := (H[j + 2]! - L[j + 1]!) * 2 ^ dtl with hsigdef
        refine hseg j _ _ (fx sig) hj2 (by rw [tfx_sub]; linarith [le_piHi]) fun t ht => ?_
        set x : ℝ := ((j + 1 : ℕ) : ℝ) / 2 ^ dtl with hx
        set y : ℝ := ((j + 2 : ℕ) : ℝ) / 2 ^ dtl with hy
        have hyx : y - x = 1 / 2 ^ dtl := by rw [hx, hy]; push_cast; field_simp; ring
        have hxy : x < y := by rw [← sub_pos, hyx]; positivity
        have htx : t ≤ x := by rw [hx]; push_cast; exact ht.2
        have hsec : Real.log (f x) + (Real.log (f y) - Real.log (f x)) / (y - x) * (t - x) ≤ Real.log (f t) :=
          secant_left hconv hxy htx
        have hLx : fx L[j + 1]! ≤ Real.log (f x) := (hLH (j + 1) (by omega) hj2).2.1
        have hHy : Real.log (f y) ≤ fx H[j + 2]! := (hLH (j + 2) (by omega) h2j).2.2
        have hfsig : fx sig = (fx H[j + 2]! - fx L[j + 1]!) * 2 ^ dtl := by
          rw [hsigdef, fx_eq, fx_eq, fx_eq]; push_cast; ring
        have hslope : (Real.log (f y) - Real.log (f x)) / (y - x) ≤ fx sig := by
          rw [div_le_iff₀ (sub_pos.2 hxy), hyx, hfsig]
          have e : (fx H[j + 2]! - fx L[j + 1]!) * 2 ^ dtl * (1 / 2 ^ dtl) = fx H[j + 2]! - fx L[j + 1]! := by
            field_simp
          rw [e]; linarith
        have hm := mul_le_mul_of_nonpos_right hslope (sub_nonpos.2 htx)
        have hdiv := le_tfx_divU (sig * ((j : ℤ) + 1)) (2 ^ dtl) (by positivity)
        have e1 : fx (sig * ((j : ℤ) + 1)) / ((2 ^ dtl : ℤ) : ℝ) = fx sig * x := by
          rw [hx, fx_eq, fx_eq]; push_cast; ring
        rw [e1] at hdiv
        rw [tfx_sub]
        nlinarith [hm, hdiv, hsec, hLx]
      · simp [tfx_zero]
      · simp [tfx_zero]
    unfold segBest
    rcases max_choice (W2C.segLo k L[j + 1]! piHi j dtl lsub logs)
      (Max.max (segC2 k dtl lsub L H logs j) (segC3 k dtl ntv lsub L H logs j)) with h | h <;> rw [h]
    · exact h1
    · rcases max_choice (segC2 k dtl lsub L H logs j) (segC3 k dtl ntv lsub L H logs j) with h' | h' <;> rw [h']
      · exact h2
      · exact h3
  -- the first segment `[0, t_1]`
  have hfirst : ENNReal.ofReal (fx (W2C.segLo k L[1]! piHi 0 dtl lsub logs)) ≤
      ∫⁻ t in Ioc 0 ((((0 : ℕ) : ℝ) + 1) / 2 ^ dtl), F t := by
    have := hseg 0 L[1]! piHi 0 (by omega) hpi fun t ht => by
      rw [zero_mul, add_zero]
      exact hval 1 le_rfl (by omega) t (by simpa using ht.2)
    simpa using this
  -- the sum over the segments
  have htot : ∀ N, N + 1 ≤ ntv →
      ENNReal.ofReal (fx ((List.range N).foldl (fun acc j0 => acc + segBest k dtl ntv lsub L H logs (j0 + 1))
        (W2C.segLo k L[1]! piHi 0 dtl lsub logs))) ≤ ∫⁻ t in Ioc 0 (((N : ℝ) + 1) / 2 ^ dtl), F t := by
    intro N
    induction N with
    | zero => intro _; simpa using hfirst
    | succ N ih =>
      intro hN
      rw [foldl_range_succ, tfx_add]
      refine ENNReal.ofReal_add_le.trans ?_
      have h1 := ih (by omega)
      have h2 := hbest (N + 1) (by omega) (by omega)
      have hle0 : (0 : ℝ) ≤ ((N : ℝ) + 1) / 2 ^ dtl := by positivity
      have hle : ((N : ℝ) + 1) / 2 ^ dtl ≤ (((N + 1 : ℕ) : ℝ) + 1) / 2 ^ dtl := by
        push_cast; exact div_le_div_of_nonneg_right (by linarith) hdt.le
      calc _ ≤ (∫⁻ t in Ioc 0 (((N : ℝ) + 1) / 2 ^ dtl), F t) +
            ∫⁻ t in Ioc (((N : ℝ) + 1) / 2 ^ dtl) ((((N + 1 : ℕ) : ℝ) + 1) / 2 ^ dtl), F t := by
            refine add_le_add h1 ?_
            convert h2 using 3
            push_cast; ring_nf
        _ = _ := by
            rw [← lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl), Ioc_union_Ioc_eq_Ioc hle0 hle]
  -- halve and extend to `(0, ∞)`
  rw [ckLo_eq]
  have hT := htot (ntv - 1) (by omega)
  set total := (List.range (ntv - 1)).foldl (fun acc j0 => acc + segBest k dtl ntv lsub L H logs (j0 + 1))
    (W2C.segLo k L[1]! piHi 0 dtl lsub logs) with htotal
  have hhalf : fx (shrD total 1) ≤ 1 / 2 * fx total := by
    have := tfx_shrD_le total 1
    rw [pow_one] at this
    linarith
  calc ENNReal.ofReal (fx (shrD total 1)) ≤ ENNReal.ofReal (1 / 2 * fx total) := ENNReal.ofReal_le_ofReal hhalf
    _ = ENNReal.ofReal (1 / 2) * ENNReal.ofReal (fx total) := ENNReal.ofReal_mul (by norm_num)
    _ ≤ ENNReal.ofReal (1 / 2) * ∫⁻ t in Ioc 0 ((((ntv - 1 : ℕ) : ℝ) + 1) / 2 ^ dtl), F t := mul_le_mul_right hT _
    _ ≤ ENNReal.ofReal (1 / 2) * ∫⁻ t in Ioi (0 : ℝ), F t :=
        mul_le_mul_right (lintegral_mono_set Ioc_subset_Ioi_self) _

end BHH.W2
