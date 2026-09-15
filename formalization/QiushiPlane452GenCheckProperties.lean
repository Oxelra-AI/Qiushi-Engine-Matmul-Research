import QiushiPlane452GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane452GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 35, (plane452GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane452GenConfig.planeBasis (i.val ^^^ (plane452GenConfig.sectionCode j).val) = true
abbrev plane452GenDeadProperty (i : Fin 512) : Prop :=
  (plane452GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane452GenConfig.deadBasis (plane452GenConfig.deadCover i)) i.val = true
abbrev plane452GenSourceProperty (i : Fin 117) : Prop :=
  forall g : Nat, g ∈ plane452GenConfig.planeBasis -> spanContainsCode (plane452GenConfig.sourceBasis i) g = true
abbrev plane452GenDeadSourceProperty (i : Fin 28) : Prop :=
  forall g : Nat, g ∈ plane452GenConfig.planeBasis -> spanContainsCode (plane452GenConfig.deadBasis i) g = true
abbrev plane452GenIndicatorProperty (i : Fin 117) : Prop :=
  forall j : Fin 35, plane452GenConfig.occSys.occCoeff i j = if spanContainsCode (plane452GenConfig.sourceBasis i) (plane452GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
