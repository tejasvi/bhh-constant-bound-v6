/-
π bounds and the arcsin bounds of `BHHCert/Leaf.lean` (module A).
-/
import BHH.Ivl.Phi

open BHH.Cert Real

namespace BHH

lemma piLo_le : fx piLo ≤ π := by
  have h := Real.pi_gt_d20
  have : fx piLo ≤ 3.14159265358979323846 := by
    unfold fx piLo PR; norm_num
  linarith

lemma le_piHi : π ≤ fx piHi := by
  have h := Real.pi_lt_d20
  have : (3.14159265358979323847 : ℝ) ≤ fx piHi := by
    unfold fx piHi PR; norm_num
  linarith

lemma piErr_nonneg : 0 ≤ piErr := by unfold piErr piHi piLo; norm_num

lemma ivMem_pi : ivMem π piIv := by
  unfold ivMem piIv
  have h1 := piLo_le
  have h2 := le_piHi
  unfold fx at h1 h2
  have hS : (0:ℝ) < 2 ^ PR := by positivity
  constructor
  · rw [div_le_iff₀ hS] at h1; simpa using h1
  · rw [le_div_iff₀ hS] at h2; simpa using h2

lemma fx_le_iff {a b : ℤ} : fx a ≤ fx b ↔ a ≤ b := by
  unfold fx
  rw [div_le_div_iff_of_pos_right (by positivity)]
  exact_mod_cast Iff.rfl

lemma fx_pos_iff {a : ℤ} : 0 < fx a ↔ 0 < a := by
  unfold fx; constructor
  · intro h; have : (0:ℝ) < a := by
      have hS : (0:ℝ) < 2 ^ PR := by positivity
      exact (div_pos_iff_of_pos_right hS).mp h
    exact_mod_cast this
  · intro h; positivity

lemma fx_nonneg_iff {a : ℤ} : 0 ≤ fx a ↔ 0 ≤ a := by
  unfold fx; constructor
  · intro h; have hS : (0:ℝ) < 2 ^ PR := by positivity
    have : (0:ℝ) ≤ a := by
      rcases le_or_gt 0 (a:ℝ) with h' | h'
      · exact h'
      · exact absurd h (not_le.mpr (div_neg_of_neg_of_pos h' hS))
    exact_mod_cast this
  · intro h; positivity

/-- the candidate point is a valid argument of `cs` and lies in `[0, π/2]` -/
lemma asin_arg {a : ℤ} (h0 : 0 ≤ a) (h1 : 2 * a ≤ piLo) :
    a.natAbs ≤ 7 * ONE.toNat ∧ 0 ≤ fx a ∧ fx a ≤ π / 2 := by
  have hpl : piLo ≤ 4 * ONE := by unfold piLo ONE; norm_num
  have hONE : ONE.toNat = 2 ^ PR := by simp [ONE, PR]
  refine ⟨?_, fx_nonneg_iff.mpr h0, ?_⟩
  · have : a ≤ 2 * ONE := by omega
    have hO : (ONE : ℤ) = ((ONE.toNat : ℕ) : ℤ) := by simp [ONE]
    omega
  · have h2 : fx (2 * a) ≤ fx piLo := fx_le_iff.mpr h1
    have : fx (2 * a) = 2 * fx a := by unfold fx; push_cast; ring
    linarith [piLo_le]

lemma ivMem_hi_le {x : ℝ} {a : Iv} (h : ivMem x a) : x ≤ fx a.hi := by
  obtain ⟨_, h2⟩ := h
  unfold fx; rw [le_div_iff₀ (by positivity)]; exact h2

lemma ivMem_lo_le {x : ℝ} {a : Iv} (h : ivMem x a) : fx a.lo ≤ x := by
  obtain ⟨h1, _⟩ := h
  unfold fx; rw [div_le_iff₀ (by positivity)]; exact h1

theorem asinHi_sound (cs : ℤ → Iv × Iv) (hcs : CosSinSound cs) (cand : AsinFn) (x : ℤ) :
    Real.arcsin (fx x) ≤ fx (asinHi cs cand x) := by
  unfold asinHi
  dsimp only
  have hhalf : π / 2 ≤ fx (shrU piHi 1) := by
    have := le_shrU piHi 1
    unfold fx
    rw [le_div_iff₀ (by positivity)]
    have h2 := le_piHi
    unfold fx at h2
    have hS : (0:ℝ) < 2 ^ PR := by positivity
    have : π * 2 ^ PR ≤ piHi := by rw [le_div_iff₀ hS] at h2; exact h2
    linarith
  split_ifs with h1 h2
  · obtain ⟨harg, ha0, ha1⟩ := asin_arg h1.1 h1.2
    have hsin := (hcs _ harg).2
    have : fx x ≤ Real.sin (fx (cand x + 2 ^ (PR - 40))) :=
      le_trans (fx_le_iff.mpr h2) (ivMem_lo_le hsin)
    calc Real.arcsin (fx x) ≤ Real.arcsin (Real.sin (fx (cand x + 2 ^ (PR - 40)))) :=
          Real.arcsin_le_arcsin this
      _ = fx (cand x + 2 ^ (PR - 40)) := Real.arcsin_sin (by linarith [Real.pi_pos]) ha1
  · exact le_trans (Real.arcsin_le_pi_div_two _) hhalf
  · exact le_trans (Real.arcsin_le_pi_div_two _) hhalf

theorem asinLo_sound (cs : ℤ → Iv × Iv) (hcs : CosSinSound cs) (cand : AsinFn) (x : ℤ) (hx : 0 ≤ fx x) :
    fx (asinLo cs cand x) ≤ Real.arcsin (fx x) := by
  unfold asinLo
  dsimp only
  split_ifs with h1 h2
  · obtain ⟨harg, ha0, ha1⟩ := asin_arg h1.1 h1.2
    have hsin := (hcs _ harg).2
    have : Real.sin (fx (cand x - 2 ^ (PR - 40))) ≤ fx x :=
      le_trans (ivMem_hi_le hsin) (fx_le_iff.mpr h2)
    calc fx (cand x - 2 ^ (PR - 40)) = Real.arcsin (Real.sin (fx (cand x - 2 ^ (PR - 40)))) :=
          (Real.arcsin_sin (by linarith [Real.pi_pos]) ha1).symm
      _ ≤ Real.arcsin (fx x) := Real.arcsin_le_arcsin this
  · rw [show fx 0 = 0 by simp [fx]]; exact Real.arcsin_nonneg.mpr hx
  · rw [show fx 0 = 0 by simp [fx]]; exact Real.arcsin_nonneg.mpr hx

end BHH
