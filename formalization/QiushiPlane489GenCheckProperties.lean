import QiushiPlane489GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane489GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 32, (plane489GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane489GenConfig.planeBasis (i.val ^^^ (plane489GenConfig.sectionCode j).val) = true
abbrev plane489GenDeadProperty (i : Fin 512) : Prop :=
  (plane489GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane489GenConfig.deadBasis (plane489GenConfig.deadCover i)) i.val = true
abbrev plane489GenSourceProperty (i : Fin 371) : Prop :=
  forall g : Nat, g ∈ plane489GenConfig.planeBasis -> spanContainsCode (plane489GenConfig.sourceBasis i) g = true
abbrev plane489GenDeadSourceProperty (i : Fin 95) : Prop :=
  forall g : Nat, g ∈ plane489GenConfig.planeBasis -> spanContainsCode (plane489GenConfig.deadBasis i) g = true
abbrev plane489GenIndicatorProperty (i : Fin 371) : Prop :=
  forall j : Fin 32, plane489GenConfig.occSys.occCoeff i j = if spanContainsCode (plane489GenConfig.sourceBasis i) (plane489GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
