import QiushiPlane486GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane486GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 41, (plane486GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane486GenConfig.planeBasis (i.val ^^^ (plane486GenConfig.sectionCode j).val) = true
abbrev plane486GenDeadProperty (i : Fin 512) : Prop :=
  (plane486GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane486GenConfig.deadBasis (plane486GenConfig.deadCover i)) i.val = true
abbrev plane486GenSourceProperty (i : Fin 262) : Prop :=
  forall g : Nat, g ∈ plane486GenConfig.planeBasis -> spanContainsCode (plane486GenConfig.sourceBasis i) g = true
abbrev plane486GenDeadSourceProperty (i : Fin 86) : Prop :=
  forall g : Nat, g ∈ plane486GenConfig.planeBasis -> spanContainsCode (plane486GenConfig.deadBasis i) g = true
abbrev plane486GenIndicatorProperty (i : Fin 262) : Prop :=
  forall j : Fin 41, plane486GenConfig.occSys.occCoeff i j = if spanContainsCode (plane486GenConfig.sourceBasis i) (plane486GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
