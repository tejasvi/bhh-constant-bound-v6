/-
Module C: Prop 3.4 and its second bracket (`BracketProp` of `BHH/Interfaces.lean`).
-/
import BHH.Box.Uniform
import BHH.Box.PhiCalc

open MeasureTheory Set Real ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace BHH

/-! ## Cauchy-Schwarz and Minkowski for integrals -/

section CS

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma integral_mul_sq_le {U V : Ω → ℝ} (hU : Integrable (fun x => U x ^ 2) μ)
    (hV : Integrable (fun x => V x ^ 2) μ) (hUV : Integrable (fun x => U x * V x) μ) :
    (∫ x, U x * V x ∂μ) ^ 2 ≤ (∫ x, U x ^ 2 ∂μ) * ∫ x, V x ^ 2 ∂μ := by
  have key : ∀ t : ℝ, 0 ≤ (∫ x, V x ^ 2 ∂μ) * (t * t) + (2 * ∫ x, U x * V x ∂μ) * t +
      ∫ x, U x ^ 2 ∂μ := by
    intro t
    have e : ∀ x, (t * V x + U x) ^ 2 = (t * t) * V x ^ 2 + (2 * t) * (U x * V x) + U x ^ 2 :=
      fun x => by ring
    have h : ∫ x, (t * V x + U x) ^ 2 ∂μ = (∫ x, V x ^ 2 ∂μ) * (t * t) +
        (2 * ∫ x, U x * V x ∂μ) * t + ∫ x, U x ^ 2 ∂μ := by
      simp_rw [e]
      have h1 : Integrable (fun x => t * t * V x ^ 2 + 2 * t * (U x * V x)) μ :=
        (hV.const_mul _).add (hUV.const_mul _)
      rw [integral_add h1 hU, integral_add (hV.const_mul _) (hUV.const_mul _), integral_const_mul,
        integral_const_mul]
      ring
    rw [← h]
    exact integral_nonneg fun x => sq_nonneg _
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

lemma integral_add_sq_le {U V : Ω → ℝ} (hU : Integrable (fun x => U x ^ 2) μ)
    (hV : Integrable (fun x => V x ^ 2) μ) (hUV : Integrable (fun x => U x * V x) μ) :
    ∫ x, (U x + V x) ^ 2 ∂μ ≤ (√(∫ x, U x ^ 2 ∂μ) + √(∫ x, V x ^ 2 ∂μ)) ^ 2 := by
  have e : ∀ x, (U x + V x) ^ 2 = U x ^ 2 + 2 * (U x * V x) + V x ^ 2 := fun x => by ring
  simp_rw [e]
  have h1 : Integrable (fun x => U x ^ 2 + 2 * (U x * V x)) μ := hU.add (hUV.const_mul 2)
  rw [integral_add h1 hV, integral_add hU (hUV.const_mul 2), integral_const_mul]
  have hA : 0 ≤ ∫ x, U x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hB : 0 ≤ ∫ x, V x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hC : ∫ x, U x * V x ∂μ ≤ √(∫ x, U x ^ 2 ∂μ) * √(∫ x, V x ^ 2 ∂μ) := by
    rw [← Real.sqrt_mul hA]
    exact (le_abs_self _).trans (Real.abs_le_sqrt (integral_mul_sq_le hU hV hUV))
  rw [add_sq, Real.sq_sqrt hA, Real.sq_sqrt hB]
  linarith

end CS

/-! ## Expectations of linear forms in the centred coordinates -/

section Lin

variable {m : ℕ} {lo hi : Fin m → ℝ}

lemma mem_rbox_iff {x : Fin m → ℝ} : x ∈ rbox lo hi ↔ ∀ d, lo d ≤ x d ∧ x d ≤ hi d := by
  simp only [rbox, Set.mem_univ_pi, Set.mem_Icc]

lemma abs_mid_le {x : Fin m → ℝ} (hx : x ∈ rbox lo hi) (d : Fin m) :
    |x d - (lo d + hi d) / 2| ≤ (hi d - lo d) / 2 := by
  have := mem_rbox_iff.1 hx d
  rw [abs_le]; constructor <;> linarith [this.1, this.2]

/-- integrability of a function bounded on the box under the uniform measure -/
lemma int_of_bdd (h : ∀ d, lo d < hi d) {g : (Fin m → ℝ) → ℝ}
    (hg : AEStronglyMeasurable g (unifBox lo hi)) (C : ℝ) (hb : ∀ x ∈ rbox lo hi, |g x| ≤ C) :
    Integrable g (unifBox lo hi) := by
  have := unifBox_isProb h
  exact Integrable.mono' (integrable_const C) hg
    ((unifBox_ae_mem h).mono fun x hx => by simpa [Real.norm_eq_abs] using hb x hx)

lemma measurable_mid (d : Fin m) (c : ℝ) : Measurable fun x : Fin m → ℝ => x d - c := by
  fun_prop

lemma int_mid (h : ∀ d, lo d < hi d) (d : Fin m) :
    Integrable (fun x => x d - (lo d + hi d) / 2) (unifBox lo hi) :=
  int_of_bdd h (measurable_mid d _).aestronglyMeasurable _ fun _ hx => abs_mid_le hx d

lemma int_mid_mul (h : ∀ d, lo d < hi d) (d e : Fin m) :
    Integrable (fun x => (x d - (lo d + hi d) / 2) * (x e - (lo e + hi e) / 2)) (unifBox lo hi) :=
  int_of_bdd h ((measurable_mid d _).mul (measurable_mid e _)).aestronglyMeasurable
    ((hi d - lo d) / 2 * ((hi e - lo e) / 2)) fun _ hx => by
      rw [abs_mul]
      exact mul_le_mul (abs_mid_le hx d) (abs_mid_le hx e) (abs_nonneg _)
        (by linarith [h d])

/-- the linear part `L(x) = Σ_d b_d (x_d - c_d)` -/
def linPart (lo hi b : Fin m → ℝ) (x : Fin m → ℝ) : ℝ := ∑ d, b d * (x d - (lo d + hi d) / 2)

lemma measurable_linPart (b : Fin m → ℝ) : Measurable (linPart lo hi b) :=
  Finset.measurable_sum _ fun d _ => (measurable_mid d _).const_mul (b d)

lemma abs_linPart_le (b : Fin m → ℝ) {x : Fin m → ℝ} (hx : x ∈ rbox lo hi) :
    |linPart lo hi b x| ≤ ∑ d, |b d| * (hi d - lo d) / 2 := by
  unfold linPart
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  rw [abs_mul, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (abs_mid_le hx d) (abs_nonneg _)

lemma integral_linPart (h : ∀ d, lo d < hi d) (b : Fin m → ℝ) :
    ∫ x, linPart lo hi b x ∂unifBox lo hi = 0 := by
  unfold linPart
  rw [integral_finsetSum _ fun d _ => (int_mid h d).const_mul (b d)]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [integral_const_mul, integral_unifBox_mid h d, mul_zero]

lemma integral_mid_mul_linPart (h : ∀ d, lo d < hi d) (b : Fin m → ℝ) (d₀ : Fin m) :
    ∫ x, (x d₀ - (lo d₀ + hi d₀) / 2) * linPart lo hi b x ∂unifBox lo hi =
      b d₀ * (hi d₀ - lo d₀) ^ 2 / 12 := by
  unfold linPart
  simp_rw [Finset.mul_sum]
  have e : ∀ d (x : Fin m → ℝ), (x d₀ - (lo d₀ + hi d₀) / 2) * (b d * (x d - (lo d + hi d) / 2)) =
      b d * ((x d₀ - (lo d₀ + hi d₀) / 2) * (x d - (lo d + hi d) / 2)) := fun d x => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun d _ => (int_mid_mul h d₀ d).const_mul (b d)]
  rw [Finset.sum_eq_single d₀]
  · rw [integral_const_mul]
    simp_rw [← sq]
    rw [integral_unifBox_mid_sq h d₀]; ring
  · intro d _ hd
    rw [integral_const_mul, integral_unifBox_mid_mul h (Ne.symm hd), mul_zero]
  · intro hd; exact absurd (Finset.mem_univ d₀) hd

lemma integral_linPart_sq (h : ∀ d, lo d < hi d) (b : Fin m → ℝ) :
    ∫ x, linPart lo hi b x ^ 2 ∂unifBox lo hi = ∑ d, (b d) ^ 2 * (hi d - lo d) ^ 2 / 12 := by
  have e : ∀ x, linPart lo hi b x ^ 2 =
      ∑ d, b d * ((x d - (lo d + hi d) / 2) * linPart lo hi b x) := fun x => by
    have : linPart lo hi b x ^ 2 = (∑ d, b d * (x d - (lo d + hi d) / 2)) * linPart lo hi b x := by
      rw [sq]; rfl
    rw [this, Finset.sum_mul]
    exact Finset.sum_congr rfl fun d _ => by ring
  simp_rw [e]
  have hint : ∀ d, Integrable (fun x => (x d - (lo d + hi d) / 2) * linPart lo hi b x)
      (unifBox lo hi) := by
    intro d
    unfold linPart
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum _ fun e _ => by
      have := (int_mid_mul h d e).const_mul (b e)
      refine this.congr (ae_of_all _ fun x => ?_)
      simp only; ring
  rw [integral_finsetSum _ fun d _ => (hint d).const_mul (b d)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [integral_const_mul, integral_mid_mul_linPart h b d]
  ring

end Lin

/-! ## Prop 3.4 in expectation form -/

section Main

variable {n : ℕ} {lo hi : Fin n → ℝ}

/-- Jensen part: `E φ(Z) ≥ φ(a + R̄)` -/
lemma jensen_part (h : ∀ d, lo d < hi d) {s a τ Rbar M : ℝ} (b : Fin n → ℝ) {ρ : (Fin n → ℝ) → ℝ}
    (hs : 0 < s) (hτ : 0 < τ) (hτa : τ ≤ a) (hρm : Measurable ρ)
    (hρb : ∀ x ∈ rbox lo hi, 0 ≤ ρ x ∧ ρ x ≤ M)
    (hZτ : ∀ x ∈ rbox lo hi, τ ≤ a + linPart lo hi b x + ρ x)
    (hEρ : ∫ x, ρ x ∂unifBox lo hi ≤ Rbar) :
    phiS s (a + Rbar) ≤ ∫ x, phiS s (a + linPart lo hi b x + ρ x) ∂unifBox lo hi := by
  have hP := unifBox_isProb h
  have hae := unifBox_ae_mem h
  set Z : (Fin n → ℝ) → ℝ := fun x => a + linPart lo hi b x + ρ x with hZdef
  have hZm : Measurable Z := (measurable_const.add (measurable_linPart b)).add hρm
  set B := ∑ d, |b d| * (hi d - lo d) / 2
  have iρ : Integrable ρ (unifBox lo hi) :=
    int_of_bdd h hρm.aestronglyMeasurable M fun x hx => by
      rw [abs_of_nonneg (hρb x hx).1]; exact (hρb x hx).2
  have iL : Integrable (linPart lo hi b) (unifBox lo hi) :=
    int_of_bdd h (measurable_linPart b).aestronglyMeasurable B fun x hx => abs_linPart_le b hx
  have iZ : Integrable Z (unifBox lo hi) := ((integrable_const a).add iL).add iρ
  have hEZ : ∫ x, Z x ∂unifBox lo hi = a + ∫ x, ρ x ∂unifBox lo hi := by
    simp only [hZdef]
    have iaL : Integrable (fun x => a + linPart lo hi b x) (unifBox lo hi) := (integrable_const a).add iL
    rw [integral_add iaL iρ, integral_add (integrable_const a) iL, integral_linPart h b, integral_const]
    simp
  have hEρ0 : 0 ≤ ∫ x, ρ x ∂unifBox lo hi :=
    integral_nonneg_of_ae (hae.mono fun x hx => (hρb x hx).1)
  set mZ := ∫ x, Z x ∂unifBox lo hi
  have hmZ : τ ≤ mZ := by rw [hEZ]; linarith
  have hmZ0 : 0 < mZ := hτ.trans_le hmZ
  have iφ : Integrable (fun x => phiS s (Z x)) (unifBox lo hi) := by
    refine int_of_bdd h (hZm.pow_const (-s)).aestronglyMeasurable (phiS s τ) fun x hx => ?_
    have hz := hZτ x hx
    rw [abs_of_pos (phiS_pos s (hτ.trans_le hz))]
    exact phiS_anti hs.le hτ hz
  have ig : Integrable (fun x => phiS s mZ + dphi s mZ * (Z x - mZ)) (unifBox lo hi) :=
    (integrable_const _).add ((iZ.sub (integrable_const _)).const_mul _)
  have key : ∫ x, (phiS s mZ + dphi s mZ * (Z x - mZ)) ∂unifBox lo hi ≤
      ∫ x, phiS s (Z x) ∂unifBox lo hi := by
    refine integral_mono_ae ig iφ (hae.mono fun x hx => ?_)
    have := (phiS_taylor hs hτ (hZτ x hx) hmZ).1
    show phiS s mZ + dphi s mZ * (Z x - mZ) ≤ phiS s (Z x)
    linarith
  have hval : ∫ x, (phiS s mZ + dphi s mZ * (Z x - mZ)) ∂unifBox lo hi = phiS s mZ := by
    have i3 : Integrable (fun x => dphi s mZ * (Z x - mZ)) (unifBox lo hi) :=
      (iZ.sub (integrable_const _)).const_mul _
    rw [integral_add (integrable_const _) i3, integral_const_mul, integral_sub iZ (integrable_const _)]
    simp [show ∫ x, Z x ∂unifBox lo hi - mZ = 0 from sub_self _]
  have hanti : phiS s (a + Rbar) ≤ phiS s mZ := phiS_anti hs.le hmZ0 (by rw [hEZ]; linarith)
  linarith

/-- Taylor part: `E[Δ₀ φ(Z)] ≥ φ'(p) b₀ h₀²/12 - |φ'(p)| (h₀/2) R̄ - (h₀/4) φ''(τ) E(Z - p)²` -/
lemma taylor_part (h : ∀ d, lo d < hi d) (d₀ : Fin n) {s a p τ Rbar M : ℝ} (b : Fin n → ℝ)
    {ρ : (Fin n → ℝ) → ℝ} (hs : 0 < s) (hτ : 0 < τ) (hp : τ ≤ p) (hρm : Measurable ρ)
    (hρb : ∀ x ∈ rbox lo hi, 0 ≤ ρ x ∧ ρ x ≤ M)
    (hZτ : ∀ x ∈ rbox lo hi, τ ≤ a + linPart lo hi b x + ρ x)
    (hEρ : ∫ x, ρ x ∂unifBox lo hi ≤ Rbar) :
    dphi s p * (b d₀ * (hi d₀ - lo d₀) ^ 2 / 12) - |dphi s p| * ((hi d₀ - lo d₀) / 2) * Rbar
      - (hi d₀ - lo d₀) / 4 * d2phi s τ * ∫ x, (a + linPart lo hi b x + ρ x - p) ^ 2 ∂unifBox lo hi
    ≤ ∫ x, (x d₀ - (lo d₀ + hi d₀) / 2) * phiS s (a + linPart lo hi b x + ρ x) ∂unifBox lo hi := by
  have hP := unifBox_isProb h
  have hae := unifBox_ae_mem h
  set Z : (Fin n → ℝ) → ℝ := fun x => a + linPart lo hi b x + ρ x with hZdef
  set Δ : (Fin n → ℝ) → ℝ := fun x => x d₀ - (lo d₀ + hi d₀) / 2 with hΔdef
  set h0 := hi d₀ - lo d₀
  set K := d2phi s τ
  have hh0 : 0 < h0 := sub_pos.2 (h d₀)
  have hK : 0 < K := d2phi_pos hs hτ
  have hZm : Measurable Z := (measurable_const.add (measurable_linPart b)).add hρm
  have hΔm : Measurable Δ := measurable_mid d₀ _
  have hΔb : ∀ x ∈ rbox lo hi, |Δ x| ≤ h0 / 2 := fun x hx => abs_mid_le hx d₀
  set B := ∑ d, |b d| * (hi d - lo d) / 2
  have hLb : ∀ x ∈ rbox lo hi, |linPart lo hi b x| ≤ B := fun x hx => abs_linPart_le b hx
  have hM : ∀ x ∈ rbox lo hi, |ρ x| ≤ M := fun x hx => by
    rw [abs_of_nonneg (hρb x hx).1]; exact (hρb x hx).2
  have iρ : Integrable ρ (unifBox lo hi) := int_of_bdd h hρm.aestronglyMeasurable M hM
  have iΔ : Integrable Δ (unifBox lo hi) := int_mid h d₀
  have iΔL : Integrable (fun x => Δ x * linPart lo hi b x) (unifBox lo hi) :=
    int_of_bdd h (hΔm.mul (measurable_linPart b)).aestronglyMeasurable (h0 / 2 * B) fun x hx => by
      rw [abs_mul]; exact mul_le_mul (hΔb x hx) (hLb x hx) (abs_nonneg _) (by linarith)
  have iΔρ : Integrable (fun x => Δ x * ρ x) (unifBox lo hi) :=
    int_of_bdd h (hΔm.mul hρm).aestronglyMeasurable (h0 / 2 * M) fun x hx => by
      rw [abs_mul]; exact mul_le_mul (hΔb x hx) (hM x hx) (abs_nonneg _) (by linarith)
  have hZp : ∀ x ∈ rbox lo hi, |Z x - p| ≤ |a - p| + B + M := fun x hx => by
    have e : Z x - p = (a - p) + linPart lo hi b x + ρ x := by simp only [hZdef]; ring
    rw [e]
    exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add le_rfl (hLb x hx))) (hM x hx))
  have iZp2 : Integrable (fun x => (Z x - p) ^ 2) (unifBox lo hi) :=
    int_of_bdd h ((hZm.sub_const p).pow_const 2).aestronglyMeasurable ((|a - p| + B + M) ^ 2)
      fun x hx => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hZp x hx) 2
  have iΔφ : Integrable (fun x => Δ x * phiS s (Z x)) (unifBox lo hi) := by
    refine int_of_bdd h (hΔm.mul (hZm.pow_const (-s))).aestronglyMeasurable (h0 / 2 * phiS s τ)
      fun x hx => ?_
    have hz := hZτ x hx
    rw [abs_mul, abs_of_pos (phiS_pos s (hτ.trans_le hz))]
    exact mul_le_mul (hΔb x hx) (phiS_anti hs.le hτ hz) (phiS_pos s (hτ.trans_le hz)).le (by linarith)
  -- the minorant
  set g : (Fin n → ℝ) → ℝ := fun x => phiS s p * Δ x +
    dphi s p * (Δ x * linPart lo hi b x + Δ x * ρ x + (a - p) * Δ x) - h0 / 2 * (K / 2) * (Z x - p) ^ 2
    with hgdef
  have i1 : Integrable (fun x => Δ x * linPart lo hi b x + Δ x * ρ x + (a - p) * Δ x) (unifBox lo hi) :=
    (iΔL.add iΔρ).add (iΔ.const_mul _)
  have i2 : Integrable (fun x => phiS s p * Δ x +
      dphi s p * (Δ x * linPart lo hi b x + Δ x * ρ x + (a - p) * Δ x)) (unifBox lo hi) :=
    (iΔ.const_mul _).add (i1.const_mul _)
  have ig : Integrable g (unifBox lo hi) := i2.sub (iZp2.const_mul _)
  have hle : ∫ x, g x ∂unifBox lo hi ≤ ∫ x, Δ x * phiS s (Z x) ∂unifBox lo hi := by
    refine integral_mono_ae ig iΔφ (hae.mono fun x hx => ?_)
    obtain ⟨t1, t2⟩ := phiS_taylor hs hτ (hZτ x hx) hp
    have hΔx := abs_le.1 (hΔb x hx)
    set ω := phiS s (Z x) - phiS s p - dphi s p * (Z x - p)
    have hω : -(h0 / 2) * ω ≤ Δ x * ω := by nlinarith [mul_nonneg (by linarith : 0 ≤ Δ x + h0 / 2) t1]
    have e : Δ x * phiS s (Z x) = phiS s p * Δ x +
        dphi s p * (Δ x * linPart lo hi b x + Δ x * ρ x + (a - p) * Δ x) + Δ x * ω := by
      simp only [ω, hZdef]; ring
    simp only [hgdef]
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left t2 (by linarith : (0:ℝ) ≤ h0 / 2)]
  have hgval : ∫ x, g x ∂unifBox lo hi = dphi s p * (b d₀ * h0 ^ 2 / 12 + ∫ x, Δ x * ρ x ∂unifBox lo hi)
      - h0 / 2 * (K / 2) * ∫ x, (Z x - p) ^ 2 ∂unifBox lo hi := by
    simp only [hgdef]
    have i5 : Integrable (fun x => Δ x * linPart lo hi b x + Δ x * ρ x) (unifBox lo hi) := iΔL.add iΔρ
    rw [integral_sub i2 (iZp2.const_mul _), integral_add (iΔ.const_mul _) (i1.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_add i5 (iΔ.const_mul _), integral_add iΔL iΔρ, integral_const_mul]
    have h1 : ∫ x, Δ x ∂unifBox lo hi = 0 := integral_unifBox_mid h d₀
    have h2 : ∫ x, Δ x * linPart lo hi b x ∂unifBox lo hi = b d₀ * h0 ^ 2 / 12 :=
      integral_mid_mul_linPart h b d₀
    rw [h1, h2]
    ring
  -- `|E[Δ ρ]| ≤ (h₀/2) E ρ`
  have hΔρ : |∫ x, Δ x * ρ x ∂unifBox lo hi| ≤ h0 / 2 * Rbar := by
    have hρ0 : 0 ≤ ∫ x, ρ x ∂unifBox lo hi := integral_nonneg_of_ae (hae.mono fun x hx => (hρb x hx).1)
    refine (abs_integral_le_integral_abs).trans ?_
    have : ∫ x, |Δ x * ρ x| ∂unifBox lo hi ≤ ∫ x, h0 / 2 * ρ x ∂unifBox lo hi := by
      refine integral_mono_ae iΔρ.abs (iρ.const_mul _) (hae.mono fun x hx => ?_)
      show |Δ x * ρ x| ≤ h0 / 2 * ρ x
      rw [abs_mul, abs_of_nonneg (hρb x hx).1]
      exact mul_le_mul_of_nonneg_right (hΔb x hx) (hρb x hx).1
    rw [integral_const_mul] at this
    nlinarith
  have hd : -(|dphi s p| * (h0 / 2 * Rbar)) ≤ dphi s p * ∫ x, Δ x * ρ x ∂unifBox lo hi := by
    have := abs_mul (dphi s p) (∫ x, Δ x * ρ x ∂unifBox lo hi)
    have h3 := neg_abs_le (dphi s p * ∫ x, Δ x * ρ x ∂unifBox lo hi)
    have h4 : |dphi s p| * |∫ x, Δ x * ρ x ∂unifBox lo hi| ≤ |dphi s p| * (h0 / 2 * Rbar) :=
      mul_le_mul_of_nonneg_left hΔρ (abs_nonneg _)
    linarith
  have hfin := hle
  rw [hgval] at hfin
  linarith

/-- `E(ρ + κ)² = Eρ² + 2κ Eρ + κ²` -/
lemma integral_add_const_sq (h : ∀ d, lo d < hi d) {M : ℝ} {ρ : (Fin n → ℝ) → ℝ} (hρm : Measurable ρ)
    (hρb : ∀ x ∈ rbox lo hi, 0 ≤ ρ x ∧ ρ x ≤ M) (κ : ℝ) :
    ∫ x, (ρ x + κ) ^ 2 ∂unifBox lo hi =
      ∫ x, ρ x ^ 2 ∂unifBox lo hi + 2 * κ * ∫ x, ρ x ∂unifBox lo hi + κ ^ 2 := by
  have hP := unifBox_isProb h
  have hM : ∀ x ∈ rbox lo hi, |ρ x| ≤ M := fun x hx => by
    rw [abs_of_nonneg (hρb x hx).1]; exact (hρb x hx).2
  have iρ : Integrable ρ (unifBox lo hi) := int_of_bdd h hρm.aestronglyMeasurable M hM
  have iρ2 : Integrable (fun x => ρ x ^ 2) (unifBox lo hi) :=
    int_of_bdd h (hρm.pow_const 2).aestronglyMeasurable (M ^ 2) fun x hx => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hM x hx) 2
  have e : ∀ x, (ρ x + κ) ^ 2 = ρ x ^ 2 + 2 * κ * ρ x + κ ^ 2 := fun x => by ring
  simp_rw [e]
  have i1 : Integrable (fun x => ρ x ^ 2 + 2 * κ * ρ x) (unifBox lo hi) := iρ2.add (iρ.const_mul _)
  rw [integral_add i1 (integrable_const _), integral_add iρ2 (iρ.const_mul _), integral_const_mul,
    integral_const]
  simp

/-- second moment of `Z - p` (Minkowski) -/
lemma second_moment_part (h : ∀ d, lo d < hi d) {a p M : ℝ} (b : Fin n → ℝ) {ρ : (Fin n → ℝ) → ℝ}
    (hρm : Measurable ρ) (hρb : ∀ x ∈ rbox lo hi, 0 ≤ ρ x ∧ ρ x ≤ M) :
    ∫ x, (a + linPart lo hi b x + ρ x - p) ^ 2 ∂unifBox lo hi ≤
      (√(∑ d, (b d) ^ 2 * (hi d - lo d) ^ 2 / 12) + √(∫ x, (ρ x + (a - p)) ^ 2 ∂unifBox lo hi)) ^ 2 := by
  set B := ∑ d, |b d| * (hi d - lo d) / 2
  have hLb : ∀ x ∈ rbox lo hi, |linPart lo hi b x| ≤ B := fun x hx => abs_linPart_le b hx
  have hVb : ∀ x ∈ rbox lo hi, |ρ x + (a - p)| ≤ M + |a - p| := fun x hx => by
    refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
    rw [abs_of_nonneg (hρb x hx).1]; exact (hρb x hx).2
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hLb _ (mem_rbox_iff.2 fun d => ⟨le_rfl, (h d).le⟩))
  have hLm := measurable_linPart (lo := lo) (hi := hi) b
  have hVm : Measurable fun x => ρ x + (a - p) := hρm.add_const _
  have iU : Integrable (fun x => linPart lo hi b x ^ 2) (unifBox lo hi) :=
    int_of_bdd h (hLm.pow_const 2).aestronglyMeasurable (B ^ 2) fun x hx => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hLb x hx) 2
  have iV : Integrable (fun x => (ρ x + (a - p)) ^ 2) (unifBox lo hi) :=
    int_of_bdd h (hVm.pow_const 2).aestronglyMeasurable ((M + |a - p|) ^ 2) fun x hx => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hVb x hx) 2
  have iUV : Integrable (fun x => linPart lo hi b x * (ρ x + (a - p))) (unifBox lo hi) :=
    int_of_bdd h (hLm.mul hVm).aestronglyMeasurable (B * (M + |a - p|)) fun x hx => by
      rw [abs_mul]; exact mul_le_mul (hLb x hx) (hVb x hx) (abs_nonneg _) hB0
  have e : ∀ x, (a + linPart lo hi b x + ρ x - p) ^ 2 = (linPart lo hi b x + (ρ x + (a - p))) ^ 2 :=
    fun x => by ring
  simp_rw [e]
  have := integral_add_sq_le iU iV iUV
  rwa [integral_linPart_sq h b] at this

/-- Prop 3.4 and the second bracket, in expectation form, with the distinguished coordinate `d₀`. -/
lemma bracket_expect (h : ∀ d, lo d < hi d) (d₀ : Fin n) (hlo : 0 ≤ lo d₀) {s a Rbar Sbar M : ℝ}
    (b : Fin n → ℝ) {ρ : (Fin n → ℝ) → ℝ} (hs : 0 < s) (hR : 0 ≤ Rbar) (hS : 0 ≤ Sbar)
    (hρm : Measurable ρ) (hρb : ∀ x ∈ rbox lo hi, 0 ≤ ρ x ∧ ρ x ≤ M)
    (hEρ : ∫ x, ρ x ∂unifBox lo hi ≤ Rbar) (hEρ2 : ∫ x, ρ x ^ 2 ∂unifBox lo hi ≤ Sbar ^ 2)
    (hτ : 0 < a - ∑ d, |b d| * (hi d - lo d) / 2) :
    (lo d₀ + hi d₀) / 2 * phiS s (a + Rbar) + dphi s a * (b d₀ * (hi d₀ - lo d₀) ^ 2 / 12)
        - |dphi s a| * ((hi d₀ - lo d₀) / 2) * Rbar
        - (hi d₀ - lo d₀) / 4 * d2phi s (a - ∑ d, |b d| * (hi d - lo d) / 2) *
          (√(∑ d, (b d) ^ 2 * (hi d - lo d) ^ 2 / 12) + Sbar) ^ 2
      ≤ ∫ x, x d₀ * phiS s (a + linPart lo hi b x + ρ x) ∂unifBox lo hi ∧
    (lo d₀ + hi d₀) / 2 * phiS s (a + Rbar) + dphi s (a + Rbar) * (b d₀ * (hi d₀ - lo d₀) ^ 2 / 12)
        - |dphi s (a + Rbar)| * ((hi d₀ - lo d₀) / 2) * Rbar
        - (hi d₀ - lo d₀) / 4 * d2phi s (a - ∑ d, |b d| * (hi d - lo d) / 2) *
          (√(∑ d, (b d) ^ 2 * (hi d - lo d) ^ 2 / 12) + √(Sbar ^ 2 + Rbar ^ 2)) ^ 2
      ≤ ∫ x, x d₀ * phiS s (a + linPart lo hi b x + ρ x) ∂unifBox lo hi := by
  set τ := a - ∑ d, |b d| * (hi d - lo d) / 2 with hτdef
  set Sb := √(∑ d, (b d) ^ 2 * (hi d - lo d) ^ 2 / 12)
  set h0 := hi d₀ - lo d₀
  set K := d2phi s τ
  have hP := unifBox_isProb h
  have hae := unifBox_ae_mem h
  have hB0 : 0 ≤ ∑ d, |b d| * (hi d - lo d) / 2 :=
    (abs_nonneg _).trans (abs_linPart_le b (mem_rbox_iff.2 fun d => ⟨le_rfl, (h d).le⟩))
  have hτa : τ ≤ a := by linarith
  have hZτ : ∀ x ∈ rbox lo hi, τ ≤ a + linPart lo hi b x + ρ x := fun x hx => by
    have h1 := abs_le.1 (abs_linPart_le b hx); have h2 := (hρb x hx).1; linarith [h1.1]
  have hh0 : 0 < h0 := sub_pos.2 (h d₀)
  have hK : 0 < K := d2phi_pos hs hτ
  have hc0 : 0 ≤ (lo d₀ + hi d₀) / 2 := by linarith [h d₀]
  have hSb : 0 ≤ Sb := Real.sqrt_nonneg _
  have hJ := jensen_part h b hs hτ hτa hρm hρb hZτ hEρ
  have hT1 := taylor_part h d₀ b hs hτ hτa hρm hρb hZτ hEρ
  have hT2 := taylor_part h d₀ b hs hτ (by linarith : τ ≤ a + Rbar) hρm hρb hZτ hEρ
  have hW1 := second_moment_part h b hρm hρb (a := a) (p := a)
  have hW2 := second_moment_part h b hρm hρb (a := a) (p := a + Rbar)
  have hρ0 : 0 ≤ ∫ x, ρ x ∂unifBox lo hi := integral_nonneg_of_ae (hae.mono fun x hx => (hρb x hx).1)
  have hV1 : √(∫ x, (ρ x + (a - a)) ^ 2 ∂unifBox lo hi) ≤ Sbar := by
    rw [integral_add_const_sq h hρm hρb]
    calc √(∫ x, ρ x ^ 2 ∂unifBox lo hi + 2 * (a - a) * ∫ x, ρ x ∂unifBox lo hi + (a - a) ^ 2)
        ≤ √(Sbar ^ 2) := Real.sqrt_le_sqrt (by simp only [sub_self]; linarith)
      _ = Sbar := Real.sqrt_sq hS
  have hV2 : √(∫ x, (ρ x + (a - (a + Rbar))) ^ 2 ∂unifBox lo hi) ≤ √(Sbar ^ 2 + Rbar ^ 2) := by
    rw [integral_add_const_sq h hρm hρb]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hW1' : ∫ x, (a + linPart lo hi b x + ρ x - a) ^ 2 ∂unifBox lo hi ≤ (Sb + Sbar) ^ 2 :=
    hW1.trans (pow_le_pow_left₀ (add_nonneg hSb (Real.sqrt_nonneg _)) (add_le_add le_rfl hV1) 2)
  have hW2' : ∫ x, (a + linPart lo hi b x + ρ x - (a + Rbar)) ^ 2 ∂unifBox lo hi ≤
      (Sb + √(Sbar ^ 2 + Rbar ^ 2)) ^ 2 :=
    hW2.trans (pow_le_pow_left₀ (add_nonneg hSb (Real.sqrt_nonneg _)) (add_le_add le_rfl hV2) 2)
  -- decomposition `x₀ φ(Z) = c₀ φ(Z) + Δ₀ φ(Z)`
  set Z : (Fin n → ℝ) → ℝ := fun x => a + linPart lo hi b x + ρ x with hZdef
  have hZm : Measurable Z := (measurable_const.add (measurable_linPart b)).add hρm
  have iφ : Integrable (fun x => phiS s (Z x)) (unifBox lo hi) := by
    refine int_of_bdd h (hZm.pow_const (-s)).aestronglyMeasurable (phiS s τ) fun x hx => ?_
    have hz := hZτ x hx
    rw [abs_of_pos (phiS_pos s (hτ.trans_le hz))]
    exact phiS_anti hs.le hτ hz
  have iΔφ : Integrable (fun x => (x d₀ - (lo d₀ + hi d₀) / 2) * phiS s (Z x)) (unifBox lo hi) := by
    refine int_of_bdd h ((measurable_mid d₀ _).mul (hZm.pow_const (-s))).aestronglyMeasurable
      (h0 / 2 * phiS s τ) fun x hx => ?_
    have hz := hZτ x hx
    rw [abs_mul, abs_of_pos (phiS_pos s (hτ.trans_le hz))]
    exact mul_le_mul (abs_mid_le hx d₀) (phiS_anti hs.le hτ hz) (phiS_pos s (hτ.trans_le hz)).le
      (by linarith)
  have hdec : ∫ x, x d₀ * phiS s (Z x) ∂unifBox lo hi = (lo d₀ + hi d₀) / 2 *
      ∫ x, phiS s (Z x) ∂unifBox lo hi +
      ∫ x, (x d₀ - (lo d₀ + hi d₀) / 2) * phiS s (Z x) ∂unifBox lo hi := by
    have e : ∀ x : Fin n → ℝ, x d₀ * phiS s (Z x) = (lo d₀ + hi d₀) / 2 * phiS s (Z x) +
        (x d₀ - (lo d₀ + hi d₀) / 2) * phiS s (Z x) := fun x => by ring
    simp_rw [e]
    rw [integral_add (iφ.const_mul _) iΔφ, integral_const_mul]
  have hc1 : (lo d₀ + hi d₀) / 2 * phiS s (a + Rbar) ≤
      (lo d₀ + hi d₀) / 2 * ∫ x, phiS s (Z x) ∂unifBox lo hi :=
    mul_le_mul_of_nonneg_left hJ hc0
  have hk : 0 ≤ h0 / 4 * K := by positivity
  constructor
  · rw [hdec]
    have := mul_le_mul_of_nonneg_left hW1' hk
    nlinarith [hT1, hc1]
  · rw [hdec]
    have := mul_le_mul_of_nonneg_left hW2' hk
    nlinarith [hT2, hc1]

end Main

/-! ## `BracketProp` -/

theorem bracketProp : BracketProp := by
  intro m lo hi s a Rbar Sbar b ρ f hlh hlo0 hs hR hS hρm hρM hEρ hEρ2
  obtain ⟨M, hM⟩ := hρM
  intro v c h0 τ Sb hτ hf rbar d1 d2 VB VA
  have hvQ : (volume (rbox lo hi)).toReal = v := volume_rbox_toReal fun d => (hlh d).le
  have hvpos : 0 < v := hvQ ▸ volume_rbox_toReal_pos hlh
  have hEρ' : ∫ x, ρ x ∂unifBox lo hi ≤ Rbar := by
    rw [setIntegral_rbox hlh, hvQ] at hEρ
    exact le_of_mul_le_mul_left (by linarith) hvpos
  have hEρ2' : ∫ x, ρ x ^ 2 ∂unifBox lo hi ≤ Sbar ^ 2 := by
    rw [setIntegral_rbox hlh, hvQ] at hEρ2
    exact le_of_mul_le_mul_left (by linarith) hvpos
  obtain ⟨hVB, hVA⟩ := bracket_expect hlh 0 hlo0 b hs hR hS hρm hM hEρ' hEρ2' hτ
  have hP := unifBox_isProb hlh
  have hτ' : 0 < τ := hτ
  set Z : (Fin (m + 1) → ℝ) → ℝ := fun x => a + linPart lo hi b x + ρ x with hZdef
  have hZτ : ∀ x ∈ rbox lo hi, τ ≤ Z x := fun x hx => by
    have h1 := abs_le.1 (abs_linPart_le b hx); have h2 := (hM x hx).1
    simp only [hZdef]; linarith [h1.1]
  have hZm : Measurable Z := (measurable_const.add (measurable_linPart b)).add hρm
  have hF0 : ∀ x ∈ rbox lo hi, 0 ≤ x 0 * phiS s (Z x) := fun x hx =>
    mul_nonneg (hlo0.trans (mem_rbox_iff.1 hx 0).1) (phiS_pos s (hτ'.trans_le (hZτ x hx))).le
  have iF : Integrable (fun x => x 0 * phiS s (Z x)) (unifBox lo hi) := by
    refine int_of_bdd hlh ((measurable_pi_apply 0).mul (hZm.pow_const (-s))).aestronglyMeasurable
      (hi 0 * phiS s τ) fun x hx => ?_
    have hz := hZτ x hx
    rw [abs_of_nonneg (hF0 x hx)]
    exact mul_le_mul (mem_rbox_iff.1 hx 0).2 (phiS_anti hs.le hτ' hz)
      (phiS_pos s (hτ'.trans_le hz)).le (hlo0.trans (hlh 0).le)
  have iF' : Integrable (fun x => x 0 * phiS s (Z x)) (volume.restrict (rbox lo hi)) := by
    rw [restrict_rbox hlh]; exact iF.smul_measure volume_rbox_ne_top
  calc ENNReal.ofReal (v * max VB VA)
      ≤ ENNReal.ofReal (∫ x in rbox lo hi, x 0 * phiS s (Z x)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [setIntegral_rbox hlh, hvQ]
        exact mul_le_mul_of_nonneg_left (max_le hVB hVA) hvpos.le
    _ = ∫⁻ x in rbox lo hi, ENNReal.ofReal (x 0 * phiS s (Z x)) :=
        ofReal_integral_eq_lintegral_ofReal iF' (ae_restrict_of_forall_mem measurableSet_rbox hF0)
    _ ≤ ∫⁻ x in rbox lo hi, f x := setLIntegral_mono' measurableSet_rbox hf

end BHH
