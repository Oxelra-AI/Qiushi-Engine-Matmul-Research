import QiushiPlane254GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane254GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 18, (plane254GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane254GenConfig.planeBasis (i.val ^^^ (plane254GenConfig.sectionCode j).val) = true
abbrev plane254GenDeadProperty (i : Fin 512) : Prop :=
  (plane254GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane254GenConfig.deadBasis (plane254GenConfig.deadCover i)) i.val = true
abbrev plane254GenSourceProperty (i : Fin 26) : Prop :=
  forall g : Nat, g ∈ plane254GenConfig.planeBasis -> spanContainsCode (plane254GenConfig.sourceBasis i) g = true
abbrev plane254GenDeadSourceProperty (i : Fin 13) : Prop :=
  forall g : Nat, g ∈ plane254GenConfig.planeBasis -> spanContainsCode (plane254GenConfig.deadBasis i) g = true
abbrev plane254GenIndicatorProperty (i : Fin 26) : Prop :=
  forall j : Fin 18, plane254GenConfig.occSys.occCoeff i j = if spanContainsCode (plane254GenConfig.sourceBasis i) (plane254GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
