import QiushiPlane449GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane449GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 15, (plane449GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane449GenConfig.planeBasis (i.val ^^^ (plane449GenConfig.sectionCode j).val) = true
abbrev plane449GenDeadProperty (i : Fin 512) : Prop :=
  (plane449GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane449GenConfig.deadBasis (plane449GenConfig.deadCover i)) i.val = true
abbrev plane449GenSourceProperty (i : Fin 56) : Prop :=
  forall g : Nat, g ∈ plane449GenConfig.planeBasis -> spanContainsCode (plane449GenConfig.sourceBasis i) g = true
abbrev plane449GenDeadSourceProperty (i : Fin 48) : Prop :=
  forall g : Nat, g ∈ plane449GenConfig.planeBasis -> spanContainsCode (plane449GenConfig.deadBasis i) g = true
abbrev plane449GenIndicatorProperty (i : Fin 56) : Prop :=
  forall j : Fin 15, plane449GenConfig.occSys.occCoeff i j = if spanContainsCode (plane449GenConfig.sourceBasis i) (plane449GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
