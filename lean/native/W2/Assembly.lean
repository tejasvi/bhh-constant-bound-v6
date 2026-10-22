/-
Assembly of `Σ_{k=6}^{kmax} C_k ≥ num/den` from checked shards (`shardOK`), the checked t-integral (`tintOK`), the
table soundness of the run, and the modules L (`laplaceBound`), D (`discBound`), T (`TIntBound`).
-/
import W2.Glue

open MeasureTheory Set Real
open scoped ENNReal

namespace BHH.W2

open W2C BHH.Cert BHH

lemma ofReal_sum_le' {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ENNReal.ofReal (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl ih)

/-- The checked claims of a production run (both directed recursions agree with every claim). -/
def ClaimsChecked (g : Grid) (dtl kmax : ℕ) (cs : List TClaim) : Prop :=
  ∀ c ∈ cs, checkClaims kmax
    (runT4 g (mkRunData g dtl true).rings (mkRunData g dtl true).tab (mkRunData g dtl true).e1lo mkPassTab true
      c.1 dtl kmax).toArray
    (runT4 g (mkRunData g dtl true).rings (mkRunData g dtl true).tab (mkRunData g dtl true).e1hi mkPassTab false
      c.1 dtl kmax).toArray c = true

lemma discOf_w_nonneg (g : Grid) (rings : Array Ring) (tab : Array (ℕ × ℤ)) (dtl ir : ℕ) :
    0 ≤ (discOf g rings tab dtl).w ir := by
  simp only [discOf]; positivity

lemma fx_nonneg_of {a : ℤ} (h : 0 ≤ a) : 0 ≤ fx a := by
  unfold fx; positivity

lemma discOf_ab_nonneg (g : Grid) (hNT : 0 < g.NT) (dtl : ℕ) (ir ir2 : ℕ) (d : ℤ) :
    0 ≤ (discOf g (mkRunData g dtl true).rings (mkRunData g dtl true).tab dtl).ab ir ir2 d := by
  simp only [discOf]
  apply fx_nonneg_of
  by_cases hidx : tidx g ir ir2 d < (mkRunData g dtl true).tab.size
  · exact (runInputs_mk g hNT dtl true).tab_nonneg _ hidx
  · rw [getElem!_neg (mkRunData g dtl true).tab (tidx g ir ir2 d) hidx]; exact le_rfl

/-- One `C_k` (`6 ≤ k ≤ kmax`): the Lean t-integral of the claimed enclosures is at most `C_k`. -/
theorem ck_bound (hT : TIntBound) {g : Grid} {dtl T kmax lsub : ℕ} {cs : List TClaim} {L H : Array (Array ℤ)}
    (hNR : 0 < (gR g).NR) (hNT : 0 < (gR g).NT) (hsh : ClaimsChecked g dtl kmax cs)
    (hcl : claimLogs (T * 2 ^ dtl) kmax cs = some (L, H))
    (hTS : TableSound (gR g) (discOf g (mkRunData g dtl true).rings (mkRunData g dtl true).tab dtl))
    (hub : ∀ ir : ℕ, 0 ≤ ubInt (mkRunData g dtl true).rings[ir]!.euHi dtl)
    (hntv : 2 ≤ T * 2 ^ dtl) {k : ℕ} (hk6 : 6 ≤ k) (hkm : k ≤ kmax) :
    ENNReal.ofReal (fx (ckLo k dtl (T * 2 ^ dtl) lsub L[k]! H[k]! (logTable (T * 2 ^ dtl * 2 ^ lsub) (dtl + lsub))))
      ≤ C k := by
  set D := discOf g (mkRunData g dtl true).rings (mkRunData g dtl true).tab dtl with hD
  have hexp : IsExpSum (fun t => Psid (gR g) hNR hNT D (k - 1) t) :=
    isExpSum_psid (gR g) hNR hNT D (k - 1) (discOf_w_nonneg g _ _ dtl) (fun ir => fx_nonneg_of (hub ir))
      (discOf_ab_nonneg g hNT dtl)
  obtain ⟨hLs, hHs, hents⟩ := claimLogs_spec hcl k (by omega) hkm
  have hcp := claim_psid hsh hNR hNT hub
  have hbounds : ∀ j, 1 ≤ j → j ≤ T * 2 ^ dtl →
      0 < Psid (gR g) hNR hNT D (k - 1) ((j : ℝ) / 2 ^ dtl) ∧
      fx (L[k]!)[j]! ≤ Real.log (Psid (gR g) hNR hNT D (k - 1) ((j : ℝ) / 2 ^ dtl)) ∧
      Real.log (Psid (gR g) hNR hNT D (k - 1) ((j : ℝ) / 2 ^ dtl)) ≤ fx (H[k]!)[j]! := by
    intro j hj1 hj2
    obtain ⟨c, hc, e, he, hcj, hek, hlm, hLv, hHv⟩ := hents j hj1 hj2
    obtain ⟨-, -, hlo, hhi⟩ := (hcp c hc).2 e he
    rw [hcj, hek] at hlo hhi
    have hlpos : (0 : ℝ) < (e.2.1 : ℝ) * 2 ^ (-e.2.2.1) := by
      have : (0 : ℝ) < e.2.1 := by exact_mod_cast hlm
      positivity
    have hpos := hlpos.trans_le hlo
    have hhm : 0 < e.2.2.2.1 := by
      by_contra h0
      push_neg at h0
      have : e.2.2.2.1 = 0 := by omega
      rw [this] at hhi
      simp at hhi
      linarith
    refine ⟨hpos, ?_, ?_⟩
    · rw [hLv]
      exact (logScaled_lo hlm _).trans (Real.log_le_log hlpos hlo)
    · rw [hHv]
      exact (Real.log_le_log hpos hhi).trans (logScaled_hi hhm _)
  have hlogs : ∀ i, 1 ≤ i → i ≤ T * 2 ^ dtl * 2 ^ lsub →
      fx (logTable (T * 2 ^ dtl * 2 ^ lsub) (dtl + lsub))[i]! ≤ Real.log ((i : ℝ) / 2 ^ (dtl + lsub)) :=
    fun i hi1 hi2 => logTable_spec _ _ hi1 hi2
  have h1 := hT k dtl (T * 2 ^ dtl) lsub (fun t => Psid (gR g) hNR hNT D (k - 1) t) L[k]! H[k]!
    (logTable (T * 2 ^ dtl * 2 ^ lsub) (dtl + lsub)) (by omega) hntv hexp hLs hHs (logTable_size _ _) hbounds hlogs
  have h2 : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ ((k : ℝ) - 3 / 2) * Real.exp (-(π * t))) *
        ENNReal.ofReal (Psid (gR g) hNR hNT D (k - 1) t) ≤
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ ((k : ℝ) - 3 / 2) * Real.exp (-(π * t))) * Psi (k - 1) t := by
    apply setLIntegral_mono' measurableSet_Ioi
    intro t ht
    exact mul_le_mul_right (discBound (gR g) hNR hNT D hTS (k - 1) (by omega) t (le_of_lt ht)) _
  exact h1.trans ((mul_le_mul_right h2 _).trans (laplaceBound k (by omega)))

/-- `Σ_{k=6}^{kmax} C_k ≥ num/den` for a production run whose shards and t-integral are checked. -/
theorem sum_C_ge (hT : TIntBound) {g : Grid} {dtl T kmax lsub num den : ℕ} {cs : List TClaim}
    (hNR : 0 < (gR g).NR) (hNT : 0 < (gR g).NT) (hsh : ClaimsChecked g dtl kmax cs)
    (htint : tintOK dtl T kmax lsub cs num den = true)
    (hTS : TableSound (gR g) (discOf g (mkRunData g dtl true).rings (mkRunData g dtl true).tab dtl))
    (hub : ∀ ir : ℕ, 0 ≤ ubInt (mkRunData g dtl true).rings[ir]!.euHi dtl)
    (hntv : 2 ≤ T * 2 ^ dtl) :
    ENNReal.ofReal ((num : ℝ) / den) ≤ ∑ k ∈ Finset.Icc 6 kmax, C k := by
  obtain ⟨L, H, hcl, hle⟩ := tintOK_spec htint
  calc ENNReal.ofReal ((num : ℝ) / den)
      ≤ ENNReal.ofReal (∑ k0 ∈ Finset.range (kmax - 5),
          fx (ckLo (k0 + 6) dtl (T * 2 ^ dtl) lsub L[k0 + 6]! H[k0 + 6]!
            (logTable (T * 2 ^ dtl * 2 ^ lsub) (dtl + lsub)))) := ENNReal.ofReal_le_ofReal hle
    _ ≤ ∑ k0 ∈ Finset.range (kmax - 5), ENNReal.ofReal
          (fx (ckLo (k0 + 6) dtl (T * 2 ^ dtl) lsub L[k0 + 6]! H[k0 + 6]!
            (logTable (T * 2 ^ dtl * 2 ^ lsub) (dtl + lsub)))) := ofReal_sum_le' _ _
    _ ≤ ∑ k0 ∈ Finset.range (kmax - 5), C (k0 + 6) := by
        apply Finset.sum_le_sum
        intro k0 hk0
        rw [Finset.mem_range] at hk0
        exact ck_bound hT hNR hNT hsh hcl hTS hub hntv (by omega) (by omega)
    _ = ∑ k ∈ Finset.Icc 6 kmax, C k := by
        rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
        apply Finset.sum_congr (by congr 1) (fun k0 _ => by rw [add_comm])

end BHH.W2
