import QiushiPlane456GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane456GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 63, (plane456GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane456GenConfig.planeBasis (i.val ^^^ (plane456GenConfig.sectionCode j).val) = true
abbrev plane456GenDeadProperty (i : Fin 512) : Prop :=
  (plane456GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane456GenConfig.deadBasis (plane456GenConfig.deadCover i)) i.val = true
abbrev plane456GenSourceProperty (i : Fin 248) : Prop :=
  forall g : Nat, g ∈ plane456GenConfig.planeBasis -> spanContainsCode (plane456GenConfig.sourceBasis i) g = true
abbrev plane456GenDeadSourceProperty (i : Fin 1) : Prop :=
  forall g : Nat, g ∈ plane456GenConfig.planeBasis -> spanContainsCode (plane456GenConfig.deadBasis i) g = true
abbrev plane456GenIndicatorProperty (i : Fin 248) : Prop :=
  forall j : Fin 63, plane456GenConfig.occSys.occCoeff i j = if spanContainsCode (plane456GenConfig.sourceBasis i) (plane456GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
