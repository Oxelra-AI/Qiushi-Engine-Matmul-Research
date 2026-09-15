import QiushiPlane315GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane315GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 28, (plane315GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane315GenConfig.planeBasis (i.val ^^^ (plane315GenConfig.sectionCode j).val) = true
abbrev plane315GenDeadProperty (i : Fin 512) : Prop :=
  (plane315GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane315GenConfig.deadBasis (plane315GenConfig.deadCover i)) i.val = true
abbrev plane315GenSourceProperty (i : Fin 74) : Prop :=
  forall g : Nat, g ∈ plane315GenConfig.planeBasis -> spanContainsCode (plane315GenConfig.sourceBasis i) g = true
abbrev plane315GenDeadSourceProperty (i : Fin 3) : Prop :=
  forall g : Nat, g ∈ plane315GenConfig.planeBasis -> spanContainsCode (plane315GenConfig.deadBasis i) g = true
abbrev plane315GenIndicatorProperty (i : Fin 74) : Prop :=
  forall j : Fin 28, plane315GenConfig.occSys.occCoeff i j = if spanContainsCode (plane315GenConfig.sourceBasis i) (plane315GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
