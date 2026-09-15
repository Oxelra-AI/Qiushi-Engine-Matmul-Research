import QiushiPlane413GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane413GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 21, (plane413GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane413GenConfig.planeBasis (i.val ^^^ (plane413GenConfig.sectionCode j).val) = true
abbrev plane413GenDeadProperty (i : Fin 512) : Prop :=
  (plane413GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane413GenConfig.deadBasis (plane413GenConfig.deadCover i)) i.val = true
abbrev plane413GenSourceProperty (i : Fin 49) : Prop :=
  forall g : Nat, g ∈ plane413GenConfig.planeBasis -> spanContainsCode (plane413GenConfig.sourceBasis i) g = true
abbrev plane413GenDeadSourceProperty (i : Fin 41) : Prop :=
  forall g : Nat, g ∈ plane413GenConfig.planeBasis -> spanContainsCode (plane413GenConfig.deadBasis i) g = true
abbrev plane413GenIndicatorProperty (i : Fin 49) : Prop :=
  forall j : Fin 21, plane413GenConfig.occSys.occCoeff i j = if spanContainsCode (plane413GenConfig.sourceBasis i) (plane413GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
