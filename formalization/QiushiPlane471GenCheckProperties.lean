import QiushiPlane471GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane471GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 63, (plane471GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane471GenConfig.planeBasis (i.val ^^^ (plane471GenConfig.sectionCode j).val) = true
abbrev plane471GenDeadProperty (i : Fin 512) : Prop :=
  (plane471GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane471GenConfig.deadBasis (plane471GenConfig.deadCover i)) i.val = true
abbrev plane471GenSourceProperty (i : Fin 304) : Prop :=
  forall g : Nat, g ∈ plane471GenConfig.planeBasis -> spanContainsCode (plane471GenConfig.sourceBasis i) g = true
abbrev plane471GenDeadSourceProperty (i : Fin 1) : Prop :=
  forall g : Nat, g ∈ plane471GenConfig.planeBasis -> spanContainsCode (plane471GenConfig.deadBasis i) g = true
abbrev plane471GenIndicatorProperty (i : Fin 304) : Prop :=
  forall j : Fin 63, plane471GenConfig.occSys.occCoeff i j = if spanContainsCode (plane471GenConfig.sourceBasis i) (plane471GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
