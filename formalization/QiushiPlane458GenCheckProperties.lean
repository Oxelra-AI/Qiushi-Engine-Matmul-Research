import QiushiPlane458GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane458GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 56, (plane458GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane458GenConfig.planeBasis (i.val ^^^ (plane458GenConfig.sectionCode j).val) = true
abbrev plane458GenDeadProperty (i : Fin 512) : Prop :=
  (plane458GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane458GenConfig.deadBasis (plane458GenConfig.deadCover i)) i.val = true
abbrev plane458GenSourceProperty (i : Fin 203) : Prop :=
  forall g : Nat, g ∈ plane458GenConfig.planeBasis -> spanContainsCode (plane458GenConfig.sourceBasis i) g = true
abbrev plane458GenDeadSourceProperty (i : Fin 7) : Prop :=
  forall g : Nat, g ∈ plane458GenConfig.planeBasis -> spanContainsCode (plane458GenConfig.deadBasis i) g = true
abbrev plane458GenIndicatorProperty (i : Fin 203) : Prop :=
  forall j : Fin 56, plane458GenConfig.occSys.occCoeff i j = if spanContainsCode (plane458GenConfig.sourceBasis i) (plane458GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
