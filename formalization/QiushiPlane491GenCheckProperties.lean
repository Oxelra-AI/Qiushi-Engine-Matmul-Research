import QiushiPlane491GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane491GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 49, (plane491GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane491GenConfig.planeBasis (i.val ^^^ (plane491GenConfig.sectionCode j).val) = true
abbrev plane491GenDeadProperty (i : Fin 512) : Prop :=
  (plane491GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane491GenConfig.deadBasis (plane491GenConfig.deadCover i)) i.val = true
abbrev plane491GenSourceProperty (i : Fin 726) : Prop :=
  forall g : Nat, g ∈ plane491GenConfig.planeBasis -> spanContainsCode (plane491GenConfig.sourceBasis i) g = true
abbrev plane491GenDeadSourceProperty (i : Fin 78) : Prop :=
  forall g : Nat, g ∈ plane491GenConfig.planeBasis -> spanContainsCode (plane491GenConfig.deadBasis i) g = true
abbrev plane491GenIndicatorProperty (i : Fin 726) : Prop :=
  forall j : Fin 49, plane491GenConfig.occSys.occCoeff i j = if spanContainsCode (plane491GenConfig.sourceBasis i) (plane491GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
