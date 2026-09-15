import QiushiPlane477GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane477GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 0, (plane477GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane477GenConfig.planeBasis (i.val ^^^ (plane477GenConfig.sectionCode j).val) = true
abbrev plane477GenDeadProperty (i : Fin 512) : Prop :=
  (plane477GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane477GenConfig.deadBasis (plane477GenConfig.deadCover i)) i.val = true
abbrev plane477GenSourceProperty (i : Fin 63) : Prop :=
  forall g : Nat, g ∈ plane477GenConfig.planeBasis -> spanContainsCode (plane477GenConfig.sourceBasis i) g = true
abbrev plane477GenDeadSourceProperty (i : Fin 63) : Prop :=
  forall g : Nat, g ∈ plane477GenConfig.planeBasis -> spanContainsCode (plane477GenConfig.deadBasis i) g = true
abbrev plane477GenIndicatorProperty (i : Fin 63) : Prop :=
  forall j : Fin 0, plane477GenConfig.occSys.occCoeff i j = if spanContainsCode (plane477GenConfig.sourceBasis i) (plane477GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
