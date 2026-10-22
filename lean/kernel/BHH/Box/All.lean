/-
Module C (box lemmas) of the Lean proof: index of the results.  Every `Prop` of `BHH/Interfaces.lean`
(`BracketProp`) and of `BHH/Box/Props.lean` is proved; `moduleC` collects them.
-/
import BHH.Box.Bracket
import BHH.Box.Event
import BHH.Box.Disks
import BHH.Box.Moments
import BHH.Box.CdfIv
import BHH.Box.Edge
import BHH.Box.Strips
import BHH.Box.StripCode

namespace BHH

/-- the staircase bounds for the edge events (measure part `stripRealProp`, code part `PB.stripCodeProp`) -/
theorem probStripsProp : ProbStripsProp := probStripsProp_of_strip stripRealProp PB.stripCodeProp

/-- all module C statements -/
theorem moduleC :
    BracketProp ∧ EventBoundProp ∧ PartitionBoundProp ∧ CdfIvProp ∧ ProbStripsProp ∧ EdgeIndepProp ∧
    StraddleProp ∧ EnlargedDisksProp ∧ UnionAreaGePiProp ∧ PointDispProp ∧ RemMaxProp ∧ RemMomentsProp :=
  ⟨bracketProp, eventBoundProp, partitionBoundProp, cdfIvProp, probStripsProp, edgeIndepProp, straddleProp,
    enlargedDisksProp, unionAreaGePiProp, pointDispProp, remMaxProp, remMomentsProp⟩

end BHH
