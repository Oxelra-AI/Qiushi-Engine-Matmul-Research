import QiushiPlane475GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane475GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 56, (plane475GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane475GenConfig.planeBasis (i.val ^^^ (plane475GenConfig.sectionCode j).val) = true
abbrev plane475GenDeadProperty (i : Fin 512) : Prop :=
  (plane475GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane475GenConfig.deadBasis (plane475GenConfig.deadCover i)) i.val = true
abbrev plane475GenSourceProperty (i : Fin 126) : Prop :=
  forall g : Nat, g ∈ plane475GenConfig.planeBasis -> spanContainsCode (plane475GenConfig.sourceBasis i) g = true
abbrev plane475GenDeadSourceProperty (i : Fin 7) : Prop :=
  forall g : Nat, g ∈ plane475GenConfig.planeBasis -> spanContainsCode (plane475GenConfig.deadBasis i) g = true
abbrev plane475GenIndicatorProperty (i : Fin 126) : Prop :=
  forall j : Fin 56, plane475GenConfig.occSys.occCoeff i j = if spanContainsCode (plane475GenConfig.sourceBasis i) (plane475GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
