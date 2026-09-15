import QiushiPlane466GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane466GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 50, (plane466GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane466GenConfig.planeBasis (i.val ^^^ (plane466GenConfig.sectionCode j).val) = true
abbrev plane466GenDeadProperty (i : Fin 512) : Prop :=
  (plane466GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane466GenConfig.deadBasis (plane466GenConfig.deadCover i)) i.val = true
abbrev plane466GenSourceProperty (i : Fin 210) : Prop :=
  forall g : Nat, g ∈ plane466GenConfig.planeBasis -> spanContainsCode (plane466GenConfig.sourceBasis i) g = true
abbrev plane466GenDeadSourceProperty (i : Fin 13) : Prop :=
  forall g : Nat, g ∈ plane466GenConfig.planeBasis -> spanContainsCode (plane466GenConfig.deadBasis i) g = true
abbrev plane466GenIndicatorProperty (i : Fin 210) : Prop :=
  forall j : Fin 50, plane466GenConfig.occSys.occCoeff i j = if spanContainsCode (plane466GenConfig.sourceBasis i) (plane466GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
