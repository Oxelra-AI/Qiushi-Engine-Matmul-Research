import QiushiPlane426GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane426GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 58, (plane426GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane426GenConfig.planeBasis (i.val ^^^ (plane426GenConfig.sectionCode j).val) = true
abbrev plane426GenDeadProperty (i : Fin 512) : Prop :=
  (plane426GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane426GenConfig.deadBasis (plane426GenConfig.deadCover i)) i.val = true
abbrev plane426GenSourceProperty (i : Fin 340) : Prop :=
  forall g : Nat, g ∈ plane426GenConfig.planeBasis -> spanContainsCode (plane426GenConfig.sourceBasis i) g = true
abbrev plane426GenDeadSourceProperty (i : Fin 5) : Prop :=
  forall g : Nat, g ∈ plane426GenConfig.planeBasis -> spanContainsCode (plane426GenConfig.deadBasis i) g = true
abbrev plane426GenIndicatorProperty (i : Fin 340) : Prop :=
  forall j : Fin 58, plane426GenConfig.occSys.occCoeff i j = if spanContainsCode (plane426GenConfig.sourceBasis i) (plane426GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
