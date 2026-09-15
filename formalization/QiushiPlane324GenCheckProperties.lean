import QiushiPlane324GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane324GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 14, (plane324GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane324GenConfig.planeBasis (i.val ^^^ (plane324GenConfig.sectionCode j).val) = true
abbrev plane324GenDeadProperty (i : Fin 512) : Prop :=
  (plane324GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane324GenConfig.deadBasis (plane324GenConfig.deadCover i)) i.val = true
abbrev plane324GenSourceProperty (i : Fin 31) : Prop :=
  forall g : Nat, g ∈ plane324GenConfig.planeBasis -> spanContainsCode (plane324GenConfig.sourceBasis i) g = true
abbrev plane324GenDeadSourceProperty (i : Fin 17) : Prop :=
  forall g : Nat, g ∈ plane324GenConfig.planeBasis -> spanContainsCode (plane324GenConfig.deadBasis i) g = true
abbrev plane324GenIndicatorProperty (i : Fin 31) : Prop :=
  forall j : Fin 14, plane324GenConfig.occSys.occCoeff i j = if spanContainsCode (plane324GenConfig.sourceBasis i) (plane324GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
