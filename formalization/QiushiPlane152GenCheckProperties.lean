import QiushiPlane152GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane152GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 10, (plane152GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane152GenConfig.planeBasis (i.val ^^^ (plane152GenConfig.sectionCode j).val) = true
abbrev plane152GenDeadProperty (i : Fin 512) : Prop :=
  (plane152GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane152GenConfig.deadBasis (plane152GenConfig.deadCover i)) i.val = true
abbrev plane152GenSourceProperty (i : Fin 16) : Prop :=
  forall g : Nat, g ∈ plane152GenConfig.planeBasis -> spanContainsCode (plane152GenConfig.sourceBasis i) g = true
abbrev plane152GenDeadSourceProperty (i : Fin 5) : Prop :=
  forall g : Nat, g ∈ plane152GenConfig.planeBasis -> spanContainsCode (plane152GenConfig.deadBasis i) g = true
abbrev plane152GenIndicatorProperty (i : Fin 16) : Prop :=
  forall j : Fin 10, plane152GenConfig.occSys.occCoeff i j = if spanContainsCode (plane152GenConfig.sourceBasis i) (plane152GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
