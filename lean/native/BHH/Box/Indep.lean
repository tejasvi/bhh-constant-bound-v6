/-
Module C infrastructure: functions of disjoint sets of coordinates are independent under the uniform measure on a
box; the coordinates of the points of a configuration (`xcfg`).
-/
import BHH.Box.Uniform
import BHH.Box.Props

open MeasureTheory Set Real ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace BHH

section DepOn

variable {m : ℕ}

/-- `f` depends only on the coordinates in `S` -/
def DepOn {β : Type*} (S : Finset (Fin m)) (f : (Fin m → ℝ) → β) : Prop :=
  ∀ x x' : Fin m → ℝ, (∀ d ∈ S, x d = x' d) → f x = f x'

/-- extension by zero of a point of `ℝ^S` -/
def extS (S : Finset (Fin m)) (z : S → ℝ) : Fin m → ℝ := fun d => if h : d ∈ S then z ⟨d, h⟩ else 0

lemma measurable_extS (S : Finset (Fin m)) : Measurable (extS S) := by
  refine measurable_pi_iff.2 fun d => ?_
  by_cases h : d ∈ S
  · simp only [extS, h, dite_true]; exact measurable_pi_apply _
  · simp only [extS, h, dite_false]; exact measurable_const

lemma DepOn.eq_comp {β : Type*} {S : Finset (Fin m)} {f : (Fin m → ℝ) → β} (hf : DepOn S f)
    (x : Fin m → ℝ) : f x = f (extS S (fun d : S => x d)) :=
  hf _ _ fun d hd => by simp [extS, hd]

lemma DepOn.mono {β : Type*} {S T : Finset (Fin m)} {f : (Fin m → ℝ) → β} (hf : DepOn S f)
    (hST : S ⊆ T) : DepOn T f := fun x x' h => hf x x' fun d hd => h d (hST hd)

lemma DepOn.comp {β γ : Type*} {S : Finset (Fin m)} {f : (Fin m → ℝ) → β} (hf : DepOn S f)
    (g : β → γ) : DepOn S (fun x => g (f x)) := fun x x' h => congrArg g (hf x x' h)

lemma DepOn.comp₂ {β γ δ : Type*} {S : Finset (Fin m)} {f : (Fin m → ℝ) → β} {g : (Fin m → ℝ) → γ}
    (hf : DepOn S f) (hg : DepOn S g) (u : β → γ → δ) : DepOn S (fun x => u (f x) (g x)) :=
  fun x x' h => by simp only [hf x x' h, hg x x' h]

lemma depOn_const {β : Type*} (S : Finset (Fin m)) (b : β) : DepOn S (fun _ : Fin m → ℝ => b) :=
  fun _ _ _ => rfl

/-- functions of disjoint sets of coordinates are independent under the uniform measure on a box -/
lemma indepFun_of_depOn {lo hi : Fin m → ℝ} (h : ∀ d, lo d < hi d) {β γ : Type*} [MeasurableSpace β]
    [MeasurableSpace γ] {S T : Finset (Fin m)} (hST : Disjoint S T) {f : (Fin m → ℝ) → β}
    {g : (Fin m → ℝ) → γ} (hfm : Measurable f) (hgm : Measurable g) (hf : DepOn S f) (hg : DepOn T g) :
    IndepFun f g (unifBox lo hi) := by
  have hi := (unifBox_iIndep h).indepFun_finset S T hST fun d => measurable_pi_apply d
  have h2 := hi.comp (hfm.comp (measurable_extS S)) (hgm.comp (measurable_extS T))
  have ef : f = (f ∘ extS S) ∘ (fun x (d : S) => x d) := funext fun x => hf.eq_comp x
  have eg : g = (g ∘ extS T) ∘ (fun x (d : T) => x d) := funext fun x => hg.eq_comp x
  rw [ef, eg]; exact h2

lemma integral_mul_of_depOn {lo hi : Fin m → ℝ} (h : ∀ d, lo d < hi d) {S T : Finset (Fin m)}
    (hST : Disjoint S T) {f g : (Fin m → ℝ) → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : DepOn S f) (hg : DepOn T g) :
    ∫ x, f x * g x ∂unifBox lo hi = (∫ x, f x ∂unifBox lo hi) * ∫ x, g x ∂unifBox lo hi :=
  (indepFun_of_depOn h hST hfm hgm hf hg).integral_fun_mul_eq_mul_integral hfm.aestronglyMeasurable
    hgm.aestronglyMeasurable

end DepOn

/-! ## Coordinates given by optional indices -/

section Opt

variable {m : ℕ}

/-- the coordinate `x_d` for `o = some d` (`0` for `none`; `xget` is `0` out of range) -/
def oget (x : Fin m → ℝ) (o : Option ℕ) : ℝ :=
  match o with
  | none => 0
  | some d => xget x d

/-- the set of coordinates that `oget · o` reads -/
def osupp (m : ℕ) (o : Option ℕ) : Finset (Fin m) := Finset.univ.filter fun d => o = some d.val

lemma depOn_oget (o : Option ℕ) : DepOn (osupp m o) (fun x : Fin m → ℝ => oget x o) := by
  intro x x' hx
  cases o with
  | none => rfl
  | some d =>
    simp only [oget, xget]
    split_ifs with hd
    · exact hx ⟨d, hd⟩ (by simp [osupp])
    · rfl

lemma measurable_oget (o : Option ℕ) : Measurable fun x : Fin m → ℝ => oget x o := by
  cases o with
  | none => exact measurable_const
  | some d =>
    simp only [oget, xget]
    split_ifs
    · exact measurable_pi_apply _
    · exact measurable_const

lemma continuous_oget (o : Option ℕ) : Continuous fun x : Fin m → ℝ => oget x o := by
  cases o with
  | none => exact continuous_const
  | some d =>
    simp only [oget, xget]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const

lemma osupp_disjoint {o o' : Option ℕ} (h : ∀ d, o = some d → o' ≠ some d) :
    Disjoint (osupp m o) (osupp m o') := by
  rw [Finset.disjoint_left]
  intro d hd hd'
  simp only [osupp, Finset.mem_filter, Finset.mem_univ, true_and] at hd hd'
  exact h d.val hd hd'

/-- half-width of the range of `oget · o` on the box -/
def ohalf (lo hi : Fin m → ℝ) (o : Option ℕ) : ℝ := (oget hi o - oget lo o) / 2

lemma oget_mid (lo hi : Fin m → ℝ) (o : Option ℕ) :
    oget (fun d => (lo d + hi d) / 2) o = (oget lo o + oget hi o) / 2 := by
  cases o with
  | none => simp [oget]
  | some d =>
    simp only [oget, xget]
    split_ifs <;> simp

/-- the centred coordinate `u_o(x) = x_o - c_o` -/
def ucen (lo hi : Fin m → ℝ) (o : Option ℕ) (x : Fin m → ℝ) : ℝ :=
  oget x o - oget (fun d => (lo d + hi d) / 2) o

lemma measurable_ucen (lo hi : Fin m → ℝ) (o : Option ℕ) : Measurable (ucen lo hi o) :=
  (measurable_oget o).sub_const _

lemma depOn_ucen (lo hi : Fin m → ℝ) (o : Option ℕ) : DepOn (osupp m o) (ucen lo hi o) :=
  (depOn_oget o).comp (fun t => t - oget (fun d => (lo d + hi d) / 2) o)

lemma abs_ucen_le {lo hi : Fin m → ℝ} {x : Fin m → ℝ} (hx : x ∈ rbox lo hi) (o : Option ℕ) :
    |ucen lo hi o x| ≤ ohalf lo hi o := by
  have hx' : ∀ d, lo d ≤ x d ∧ x d ≤ hi d := by
    intro d; have := hx d (Set.mem_univ d); exact ⟨this.1, this.2⟩
  unfold ucen ohalf
  rw [oget_mid]
  cases o with
  | none => simp [oget]
  | some d =>
    simp only [oget, xget]
    split_ifs with hd
    · have := hx' ⟨d, hd⟩
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
    · simp

lemma ohalf_nonneg {lo hi : Fin m → ℝ} (h : ∀ d, lo d ≤ hi d) (o : Option ℕ) : 0 ≤ ohalf lo hi o := by
  unfold ohalf
  cases o with
  | none => simp [oget]
  | some d =>
    simp only [oget, xget]
    split_ifs with hd
    · linarith [h ⟨d, hd⟩]
    · simp

/-- moments of the centred coordinate: `E u = 0`, `E u² = σ²/3`, `E u⁴ = σ⁴/5` (`σ = ohalf`) -/
lemma integral_ucen {lo hi : Fin m → ℝ} (h : ∀ d, lo d < hi d) (o : Option ℕ) :
    ∫ x, ucen lo hi o x ∂unifBox lo hi = 0 := by
  have hP := unifBox_isProb h
  unfold ucen
  cases o with
  | none => simp [oget]
  | some d =>
    simp only [oget, xget]
    split_ifs with hd
    · exact integral_unifBox_mid h ⟨d, hd⟩
    · simp

lemma integral_ucen_sq {lo hi : Fin m → ℝ} (h : ∀ d, lo d < hi d) (o : Option ℕ) :
    ∫ x, ucen lo hi o x ^ 2 ∂unifBox lo hi = ohalf lo hi o ^ 2 / 3 := by
  have hP := unifBox_isProb h
  unfold ucen ohalf
  cases o with
  | none => simp [oget]
  | some d =>
    simp only [oget, xget]
    split_ifs with hd
    · rw [integral_unifBox_mid_sq h ⟨d, hd⟩]; ring
    · simp

lemma integral_ucen_four {lo hi : Fin m → ℝ} (h : ∀ d, lo d < hi d) (o : Option ℕ) :
    ∫ x, ucen lo hi o x ^ 4 ∂unifBox lo hi = ohalf lo hi o ^ 4 / 5 := by
  have hP := unifBox_isProb h
  unfold ucen ohalf
  cases o with
  | none => simp [oget]
  | some d =>
    simp only [oget, xget]
    split_ifs with hd
    · rw [integral_unifBox_mid_four h ⟨d, hd⟩]; ring
    · simp

end Opt

/-! ## The points of a configuration -/

/-- the two coordinates of the point `j` (`y_0 = 0`, `y_1 = (x_0, 0)`, `y_j = (x_{2j-3}, x_{2j-2})`) -/
def pc1 (j : ℕ) : Option ℕ := if j = 0 then none else if j = 1 then some 0 else some (2 * j - 3)
def pc2 (j : ℕ) : Option ℕ := if j = 0 then none else if j = 1 then none else some (2 * j - 2)

lemma xcfg_eq (k : ℕ) (x : Fin (mDim k) → ℝ) (j : Fin k) :
    xcfg k x j = (oget x (pc1 j.val), oget x (pc2 j.val)) := by
  unfold xcfg pc1 pc2
  split_ifs <;> simp [oget]

lemma halfSides_eqC (k : ℕ) (lo hi : Fin (mDim k) → ℝ) (j : Fin k) :
    halfSides k lo hi j = (ohalf lo hi (pc1 j.val), ohalf lo hi (pc2 j.val)) := by
  unfold halfSides pc1 pc2 ohalf
  split_ifs <;> simp [oget]

/-- the coordinates read by the point `j` -/
def ptSupp (k : ℕ) (j : ℕ) : Finset (Fin (mDim k)) := osupp (mDim k) (pc1 j) ∪ osupp (mDim k) (pc2 j)

lemma depOn_xcfg (k : ℕ) (j : Fin k) : DepOn (ptSupp k j.val) (fun x : Fin (mDim k) → ℝ => xcfg k x j) := by
  intro x x' hx
  show xcfg k x j = xcfg k x' j
  rw [xcfg_eq, xcfg_eq]
  have h1 : oget x (pc1 j.val) = oget x' (pc1 j.val) :=
    depOn_oget (pc1 j.val) x x' fun d hd => hx d (Finset.mem_union_left _ hd)
  have h2 : oget x (pc2 j.val) = oget x' (pc2 j.val) :=
    depOn_oget (pc2 j.val) x x' fun d hd => hx d (Finset.mem_union_right _ hd)
  rw [h1, h2]

lemma pc_disjoint (i j : ℕ) (hij : i ≠ j) (a b : Bool) :
    ∀ d, (if a then pc1 i else pc2 i) = some d → (if b then pc1 j else pc2 j) ≠ some d := by
  intro d hd hd'
  simp only [pc1, pc2] at hd hd'
  cases a <;> cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hd hd' <;>
    split_ifs at hd hd' <;> simp_all <;> omega

lemma ptSupp_disjoint (k : ℕ) {i j : ℕ} (hij : i ≠ j) : Disjoint (ptSupp k i) (ptSupp k j) := by
  unfold ptSupp
  rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
  exact ⟨⟨osupp_disjoint (pc_disjoint i j hij true true), osupp_disjoint (pc_disjoint i j hij true false)⟩,
    ⟨osupp_disjoint (pc_disjoint i j hij false true), osupp_disjoint (pc_disjoint i j hij false false)⟩⟩

lemma pc12_disjoint (j : ℕ) : ∀ d, pc1 j = some d → pc2 j ≠ some d := by
  intro d hd hd'
  simp only [pc1, pc2] at hd hd'
  split_ifs at hd hd' <;> simp_all <;> omega

end BHH
