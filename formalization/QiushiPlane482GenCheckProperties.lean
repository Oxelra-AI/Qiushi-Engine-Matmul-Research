import QiushiPlane482GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane482GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 48, (plane482GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane482GenConfig.planeBasis (i.val ^^^ (plane482GenConfig.sectionCode j).val) = true
abbrev plane482GenDeadProperty (i : Fin 512) : Prop :=
  (plane482GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane482GenConfig.deadBasis (plane482GenConfig.deadCover i)) i.val = true
abbrev plane482GenSourceProperty (i : Fin 118) : Prop :=
  forall g : Nat, g ∈ plane482GenConfig.planeBasis -> spanContainsCode (plane482GenConfig.sourceBasis i) g = true
abbrev plane482GenDeadSourceProperty (i : Fin 74) : Prop :=
  forall g : Nat, g ∈ plane482GenConfig.planeBasis -> spanContainsCode (plane482GenConfig.deadBasis i) g = true
abbrev plane482GenIndicatorProperty (i : Fin 118) : Prop :=
  forall j : Fin 48, plane482GenConfig.occSys.occCoeff i j = if spanContainsCode (plane482GenConfig.sourceBasis i) (plane482GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
