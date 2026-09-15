import QiushiPlane481GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane481GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 47, (plane481GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane481GenConfig.planeBasis (i.val ^^^ (plane481GenConfig.sectionCode j).val) = true
abbrev plane481GenDeadProperty (i : Fin 512) : Prop :=
  (plane481GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane481GenConfig.deadBasis (plane481GenConfig.deadCover i)) i.val = true
abbrev plane481GenSourceProperty (i : Fin 116) : Prop :=
  forall g : Nat, g ∈ plane481GenConfig.planeBasis -> spanContainsCode (plane481GenConfig.sourceBasis i) g = true
abbrev plane481GenDeadSourceProperty (i : Fin 69) : Prop :=
  forall g : Nat, g ∈ plane481GenConfig.planeBasis -> spanContainsCode (plane481GenConfig.deadBasis i) g = true
abbrev plane481GenIndicatorProperty (i : Fin 116) : Prop :=
  forall j : Fin 47, plane481GenConfig.occSys.occCoeff i j = if spanContainsCode (plane481GenConfig.sourceBasis i) (plane481GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
