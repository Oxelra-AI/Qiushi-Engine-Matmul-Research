import QiushiPlane490GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane490GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 43, (plane490GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane490GenConfig.planeBasis (i.val ^^^ (plane490GenConfig.sectionCode j).val) = true
abbrev plane490GenDeadProperty (i : Fin 512) : Prop :=
  (plane490GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane490GenConfig.deadBasis (plane490GenConfig.deadCover i)) i.val = true
abbrev plane490GenSourceProperty (i : Fin 713) : Prop :=
  forall g : Nat, g ∈ plane490GenConfig.planeBasis -> spanContainsCode (plane490GenConfig.sourceBasis i) g = true
abbrev plane490GenDeadSourceProperty (i : Fin 84) : Prop :=
  forall g : Nat, g ∈ plane490GenConfig.planeBasis -> spanContainsCode (plane490GenConfig.deadBasis i) g = true
abbrev plane490GenIndicatorProperty (i : Fin 713) : Prop :=
  forall j : Fin 43, plane490GenConfig.occSys.occCoeff i j = if spanContainsCode (plane490GenConfig.sourceBasis i) (plane490GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
