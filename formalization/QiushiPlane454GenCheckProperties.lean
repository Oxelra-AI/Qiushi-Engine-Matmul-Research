import QiushiPlane454GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane454GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 55, (plane454GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane454GenConfig.planeBasis (i.val ^^^ (plane454GenConfig.sectionCode j).val) = true
abbrev plane454GenDeadProperty (i : Fin 512) : Prop :=
  (plane454GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane454GenConfig.deadBasis (plane454GenConfig.deadCover i)) i.val = true
abbrev plane454GenSourceProperty (i : Fin 174) : Prop :=
  forall g : Nat, g ∈ plane454GenConfig.planeBasis -> spanContainsCode (plane454GenConfig.sourceBasis i) g = true
abbrev plane454GenDeadSourceProperty (i : Fin 8) : Prop :=
  forall g : Nat, g ∈ plane454GenConfig.planeBasis -> spanContainsCode (plane454GenConfig.deadBasis i) g = true
abbrev plane454GenIndicatorProperty (i : Fin 174) : Prop :=
  forall j : Fin 55, plane454GenConfig.occSys.occCoeff i j = if spanContainsCode (plane454GenConfig.sourceBasis i) (plane454GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
