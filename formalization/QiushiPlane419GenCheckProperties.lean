import QiushiPlane419GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane419GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 24, (plane419GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane419GenConfig.planeBasis (i.val ^^^ (plane419GenConfig.sectionCode j).val) = true
abbrev plane419GenDeadProperty (i : Fin 512) : Prop :=
  (plane419GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane419GenConfig.deadBasis (plane419GenConfig.deadCover i)) i.val = true
abbrev plane419GenSourceProperty (i : Fin 59) : Prop :=
  forall g : Nat, g ∈ plane419GenConfig.planeBasis -> spanContainsCode (plane419GenConfig.sourceBasis i) g = true
abbrev plane419GenDeadSourceProperty (i : Fin 38) : Prop :=
  forall g : Nat, g ∈ plane419GenConfig.planeBasis -> spanContainsCode (plane419GenConfig.deadBasis i) g = true
abbrev plane419GenIndicatorProperty (i : Fin 59) : Prop :=
  forall j : Fin 24, plane419GenConfig.occSys.occCoeff i j = if spanContainsCode (plane419GenConfig.sourceBasis i) (plane419GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
