/-
Module D for track K: leaf soundness of `LkK k` (k = 3, 4) with kernel-checked g tables (`GraphK`) and module A's
Taylor cos/sin; standard axioms only.  The extra-term specification remains a hypothesis until it lands.
-/
import BHH.LeafSound.Final
import BHH.GraphK
import BHHCert.ShardK

open BHH.Cert

noncomputable section

namespace BHH

lemma gtK_nonneg_D (k idx : ℕ) : 0 ≤ (gtK k).gmin idx := by
  unfold gtK
  split <;> exact Int.natCast_nonneg _

lemma gtK_sound_k {k : ℕ} (hk3 : 3 ≤ k) (hk4 : k ≤ 4) : GTabSound k (gtK k) := by
  interval_cases k
  · exact gtK_sound_three
  · exact gtK_sound_four

/-- leaf soundness for track K (k = 3, 4), the extra-term specification as a hypothesis -/
theorem leafSound_K_extra (hG : GreenFormula) (hVL : VertexLemmaSeg)
    (hEx : ∀ k, 3 ≤ k → k ≤ 4 → ExtraSpec k (gtK k)) :
    ∀ k : ℕ, 3 ≤ k → k ≤ 4 → LeafSoundProp k (LkK k) := by
  intro k hk3 hk4
  have hgt := gtK_sound_k hk3 hk4
  exact leafSound_top hk3 (by omega) hgt cosSin_sound exactCand exactAsin (fun idx _ => gtK_nonneg_D k idx) hG hVL
    unionSound bracketProp remMaxProp remMomentsProp unionAreaGePiProp
    (D38.prop38Spec_of hk3 hgt cosSin_sound exactCand hG unionSoundR enlargedDisksProp unionAreaGePiProp)
    (straddleSpec_of hk3 hgt eventBoundProp straddleProp) (hEx k hk3 hk4)

/-- Module D, track K: leaf soundness of `LkK k` for k = 3, 4 (standard axioms only). -/
theorem leafSound_K_final :
    GreenFormula → VertexLemmaSeg → ∀ k : ℕ, 3 ≤ k → k ≤ 4 → LeafSoundProp k (LkK k) :=
  fun hG hVL => leafSound_K_extra hG hVL (fun _ hk3 hk4 =>
    DX.extraSpec_of hk3 (gtK_sound_k hk3 hk4) eventBoundProp partitionBoundProp probStripsProp edgeIndepProp)

end BHH
