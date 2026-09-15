import QiushiPlane430GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane430GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 36, (plane430GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane430GenConfig.planeBasis (i.val ^^^ (plane430GenConfig.sectionCode j).val) = true
abbrev plane430GenDeadProperty (i : Fin 512) : Prop :=
  (plane430GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane430GenConfig.deadBasis (plane430GenConfig.deadCover i)) i.val = true
abbrev plane430GenSourceProperty (i : Fin 57) : Prop :=
  forall g : Nat, g ∈ plane430GenConfig.planeBasis -> spanContainsCode (plane430GenConfig.sourceBasis i) g = true
abbrev plane430GenDeadSourceProperty (i : Fin 24) : Prop :=
  forall g : Nat, g ∈ plane430GenConfig.planeBasis -> spanContainsCode (plane430GenConfig.deadBasis i) g = true
abbrev plane430GenIndicatorProperty (i : Fin 57) : Prop :=
  forall j : Fin 36, plane430GenConfig.occSys.occCoeff i j = if spanContainsCode (plane430GenConfig.sourceBasis i) (plane430GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
