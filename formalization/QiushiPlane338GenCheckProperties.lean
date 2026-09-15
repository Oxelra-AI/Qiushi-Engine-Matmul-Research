import QiushiPlane338GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane338GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 16, (plane338GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane338GenConfig.planeBasis (i.val ^^^ (plane338GenConfig.sectionCode j).val) = true
abbrev plane338GenDeadProperty (i : Fin 512) : Prop :=
  (plane338GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane338GenConfig.deadBasis (plane338GenConfig.deadCover i)) i.val = true
abbrev plane338GenSourceProperty (i : Fin 21) : Prop :=
  forall g : Nat, g ∈ plane338GenConfig.planeBasis -> spanContainsCode (plane338GenConfig.sourceBasis i) g = true
abbrev plane338GenDeadSourceProperty (i : Fin 15) : Prop :=
  forall g : Nat, g ∈ plane338GenConfig.planeBasis -> spanContainsCode (plane338GenConfig.deadBasis i) g = true
abbrev plane338GenIndicatorProperty (i : Fin 21) : Prop :=
  forall j : Fin 16, plane338GenConfig.occSys.occCoeff i j = if spanContainsCode (plane338GenConfig.sourceBasis i) (plane338GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
