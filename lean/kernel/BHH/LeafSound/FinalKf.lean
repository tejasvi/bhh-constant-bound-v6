/-
Module D for the kernel-only proof with the faster untrusted candidates: leaf soundness of `LkKf k` (k = 3, 4). The proof is that of
`leafSound_K_final` (BHH/LeafSound/FinalK.lean) with `fastCand` / `fastAsin` (BHHCert/CandFast.lean) as the candidate
arguments of `leafSound_top` and `D38.prop38Spec_of`; standard axioms only.
-/
import BHH.LeafSound.FinalK
import BHHCert.ShardKf

open BHH.Cert

noncomputable section

namespace BHH

/-- Module D, kernel-only proof, fast candidates: leaf soundness of `LkKf k` for k = 3, 4 (standard axioms only). -/
theorem leafSound_Kf_final :
    GreenFormula → VertexLemmaSeg → ∀ k : ℕ, 3 ≤ k → k ≤ 4 → LeafSoundProp k (LkKf k) := by
  intro hG hVL k hk3 hk4
  have hgt := gtK_sound_k hk3 hk4
  exact leafSound_top hk3 (by omega) hgt cosSin_sound fastCand fastAsin (fun idx _ => gtK_nonneg_D k idx) hG hVL
    unionSound bracketProp remMaxProp remMomentsProp unionAreaGePiProp
    (D38.prop38Spec_of hk3 hgt cosSin_sound fastCand hG unionSoundR enlargedDisksProp unionAreaGePiProp)
    (straddleSpec_of hk3 hgt eventBoundProp straddleProp)
    (DX.extraSpec_of hk3 hgt eventBoundProp partitionBoundProp probStripsProp edgeIndepProp)

end BHH
