/-
Module D, final: leaf soundness for the track N leaf function `Lk k` (k = 3, 4, 5), from modules A, B, C, E and the
two branch specifications `Prop38Spec`, `ExtraSpec`.
-/
import BHH.LeafSound.Straddle
import BHH.Box.All
import BHH.UnionSound
import BHH.TrigTab
import BHHCert.Shard
import BHH.GraphN
import BHH.LeafSound.GtNonneg
import BHH.LeafSound.Prop38
import BHH.LeafSound.Extra

open BHH.Cert Real MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BHH

theorem leafSound_N_of (hG : GreenFormula) (hVL : VertexLemmaSeg) {k : ℕ} (hk3 : 3 ≤ k) (hk5 : k ≤ 5)
    (hgt : GTabSound k (gtN k)) (hgt0 : ∀ idx, idx < 3 ^ (pairList k).length → 0 ≤ (gtN k).gmin idx)
    (hP38 : Prop38Spec k (gtN k) cosSinTab floatCand) (hEx : ExtraSpec k (gtN k)) :
    LeafSoundProp k (Lk k) :=
  leafSound_top hk3 hk5 hgt cosSinTab_sound floatCand floatAsin hgt0 hG hVL unionSound bracketProp remMaxProp
    remMomentsProp unionAreaGePiProp hP38 (straddleSpec_of hk3 hgt eventBoundProp straddleProp) hEx

/-- leaf soundness for track N with the g tables of module E (`GraphN`, native_decide) -/
theorem leafSound_N (hG : GreenFormula) (hVL : VertexLemmaSeg)
    (hgt0 : ∀ k, 3 ≤ k → k ≤ 5 → ∀ idx, idx < 3 ^ (pairList k).length → 0 ≤ (gtN k).gmin idx)
    (hP38 : ∀ k, 3 ≤ k → k ≤ 5 → Prop38Spec k (gtN k) cosSinTab floatCand)
    (hEx : ∀ k, 3 ≤ k → k ≤ 5 → ExtraSpec k (gtN k)) :
    ∀ k : ℕ, 3 ≤ k → k ≤ 5 → LeafSoundProp k (Lk k) := by
  intro k hk3 hk5
  have hgt : GTabSound k (gtN k) := by
    interval_cases k
    · exact gtN_sound_three
    · exact gtN_sound_four
    · exact gtN_sound_five
  exact leafSound_N_of hG hVL hk3 hk5 hgt (hgt0 k hk3 hk5) (hP38 k hk3 hk5) (hEx k hk3 hk5)

/-- leaf soundness for track N: only the two branch specifications remain as hypotheses -/
theorem leafSound_N_specs (hG : GreenFormula) (hVL : VertexLemmaSeg)
    (hP38 : ∀ k, 3 ≤ k → k ≤ 5 → Prop38Spec k (gtN k) cosSinTab floatCand)
    (hEx : ∀ k, 3 ≤ k → k ≤ 5 → ExtraSpec k (gtN k)) :
    ∀ k : ℕ, 3 ≤ k → k ≤ 5 → LeafSoundProp k (Lk k) :=
  leafSound_N hG hVL gtN_nonneg_D hP38 hEx

lemma gtN_sound_k {k : ℕ} (hk3 : 3 ≤ k) (hk5 : k ≤ 5) : GTabSound k (gtN k) := by
  interval_cases k
  · exact gtN_sound_three
  · exact gtN_sound_four
  · exact gtN_sound_five

/-- leaf soundness for track N: only the extra-term specification remains as a hypothesis -/
theorem leafSound_N_extra (hG : GreenFormula) (hVL : VertexLemmaSeg)
    (hEx : ∀ k, 3 ≤ k → k ≤ 5 → ExtraSpec k (gtN k)) :
    ∀ k : ℕ, 3 ≤ k → k ≤ 5 → LeafSoundProp k (Lk k) :=
  leafSound_N_specs hG hVL
    (fun _ hk3 hk5 => D38.prop38Spec_of hk3 (gtN_sound_k hk3 hk5) cosSinTab_sound floatCand hG unionSoundR
      enlargedDisksProp unionAreaGePiProp) hEx

/-- Module D, track N: leaf soundness of the leaf function `Lk k` for k = 3, 4, 5, under the two hypotheses of the
audited statements only (the form `mainBoundsV2_of` takes). -/
theorem leafSound_N_final :
    GreenFormula → VertexLemmaSeg → ∀ k : ℕ, 3 ≤ k → k ≤ 5 → LeafSoundProp k (Lk k) :=
  fun hG hVL => leafSound_N_extra hG hVL (fun _ hk3 hk5 =>
    DX.extraSpec_of hk3 (gtN_sound_k hk3 hk5) eventBoundProp partitionBoundProp probStripsProp edgeIndepProp)

end BHH
