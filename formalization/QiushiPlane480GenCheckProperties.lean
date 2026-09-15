import QiushiPlane480GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane480GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 26, (plane480GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane480GenConfig.planeBasis (i.val ^^^ (plane480GenConfig.sectionCode j).val) = true
abbrev plane480GenDeadProperty (i : Fin 512) : Prop :=
  (plane480GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane480GenConfig.deadBasis (plane480GenConfig.deadCover i)) i.val = true
abbrev plane480GenSourceProperty (i : Fin 221) : Prop :=
  forall g : Nat, g ∈ plane480GenConfig.planeBasis -> spanContainsCode (plane480GenConfig.sourceBasis i) g = true
abbrev plane480GenDeadSourceProperty (i : Fin 101) : Prop :=
  forall g : Nat, g ∈ plane480GenConfig.planeBasis -> spanContainsCode (plane480GenConfig.deadBasis i) g = true
abbrev plane480GenIndicatorProperty (i : Fin 221) : Prop :=
  forall j : Fin 26, plane480GenConfig.occSys.occCoeff i j = if spanContainsCode (plane480GenConfig.sourceBasis i) (plane480GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
