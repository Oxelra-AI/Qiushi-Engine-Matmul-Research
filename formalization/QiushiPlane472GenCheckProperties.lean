import QiushiPlane472GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane472GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 62, (plane472GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane472GenConfig.planeBasis (i.val ^^^ (plane472GenConfig.sectionCode j).val) = true
abbrev plane472GenDeadProperty (i : Fin 512) : Prop :=
  (plane472GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane472GenConfig.deadBasis (plane472GenConfig.deadCover i)) i.val = true
abbrev plane472GenSourceProperty (i : Fin 242) : Prop :=
  forall g : Nat, g ∈ plane472GenConfig.planeBasis -> spanContainsCode (plane472GenConfig.sourceBasis i) g = true
abbrev plane472GenDeadSourceProperty (i : Fin 1) : Prop :=
  forall g : Nat, g ∈ plane472GenConfig.planeBasis -> spanContainsCode (plane472GenConfig.deadBasis i) g = true
abbrev plane472GenIndicatorProperty (i : Fin 242) : Prop :=
  forall j : Fin 62, plane472GenConfig.occSys.occCoeff i j = if spanContainsCode (plane472GenConfig.sourceBasis i) (plane472GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
