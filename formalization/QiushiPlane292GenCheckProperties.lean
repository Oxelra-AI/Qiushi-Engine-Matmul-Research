import QiushiPlane292GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane292GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 11, (plane292GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane292GenConfig.planeBasis (i.val ^^^ (plane292GenConfig.sectionCode j).val) = true
abbrev plane292GenDeadProperty (i : Fin 512) : Prop :=
  (plane292GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane292GenConfig.deadBasis (plane292GenConfig.deadCover i)) i.val = true
abbrev plane292GenSourceProperty (i : Fin 28) : Prop :=
  forall g : Nat, g ∈ plane292GenConfig.planeBasis -> spanContainsCode (plane292GenConfig.sourceBasis i) g = true
abbrev plane292GenDeadSourceProperty (i : Fin 20) : Prop :=
  forall g : Nat, g ∈ plane292GenConfig.planeBasis -> spanContainsCode (plane292GenConfig.deadBasis i) g = true
abbrev plane292GenIndicatorProperty (i : Fin 28) : Prop :=
  forall j : Fin 11, plane292GenConfig.occSys.occCoeff i j = if spanContainsCode (plane292GenConfig.sourceBasis i) (plane292GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
