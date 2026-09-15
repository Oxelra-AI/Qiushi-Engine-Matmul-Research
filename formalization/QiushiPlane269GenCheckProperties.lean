import QiushiPlane269GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane269GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 21, (plane269GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane269GenConfig.planeBasis (i.val ^^^ (plane269GenConfig.sectionCode j).val) = true
abbrev plane269GenDeadProperty (i : Fin 512) : Prop :=
  (plane269GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane269GenConfig.deadBasis (plane269GenConfig.deadCover i)) i.val = true
abbrev plane269GenSourceProperty (i : Fin 30) : Prop :=
  forall g : Nat, g ∈ plane269GenConfig.planeBasis -> spanContainsCode (plane269GenConfig.sourceBasis i) g = true
abbrev plane269GenDeadSourceProperty (i : Fin 10) : Prop :=
  forall g : Nat, g ∈ plane269GenConfig.planeBasis -> spanContainsCode (plane269GenConfig.deadBasis i) g = true
abbrev plane269GenIndicatorProperty (i : Fin 30) : Prop :=
  forall j : Fin 21, plane269GenConfig.occSys.occCoeff i j = if spanContainsCode (plane269GenConfig.sourceBasis i) (plane269GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
