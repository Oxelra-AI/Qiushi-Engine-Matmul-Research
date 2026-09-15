import QiushiPlane433GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane433GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 31, (plane433GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane433GenConfig.planeBasis (i.val ^^^ (plane433GenConfig.sectionCode j).val) = true
abbrev plane433GenDeadProperty (i : Fin 512) : Prop :=
  (plane433GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane433GenConfig.deadBasis (plane433GenConfig.deadCover i)) i.val = true
abbrev plane433GenSourceProperty (i : Fin 63) : Prop :=
  forall g : Nat, g ∈ plane433GenConfig.planeBasis -> spanContainsCode (plane433GenConfig.sourceBasis i) g = true
abbrev plane433GenDeadSourceProperty (i : Fin 32) : Prop :=
  forall g : Nat, g ∈ plane433GenConfig.planeBasis -> spanContainsCode (plane433GenConfig.deadBasis i) g = true
abbrev plane433GenIndicatorProperty (i : Fin 63) : Prop :=
  forall j : Fin 31, plane433GenConfig.occSys.occCoeff i j = if spanContainsCode (plane433GenConfig.sourceBasis i) (plane433GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
