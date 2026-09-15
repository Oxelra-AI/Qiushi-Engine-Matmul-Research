import QiushiPlane278GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane278GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 24, (plane278GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane278GenConfig.planeBasis (i.val ^^^ (plane278GenConfig.sectionCode j).val) = true
abbrev plane278GenDeadProperty (i : Fin 512) : Prop :=
  (plane278GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane278GenConfig.deadBasis (plane278GenConfig.deadCover i)) i.val = true
abbrev plane278GenSourceProperty (i : Fin 28) : Prop :=
  forall g : Nat, g ∈ plane278GenConfig.planeBasis -> spanContainsCode (plane278GenConfig.sourceBasis i) g = true
abbrev plane278GenDeadSourceProperty (i : Fin 8) : Prop :=
  forall g : Nat, g ∈ plane278GenConfig.planeBasis -> spanContainsCode (plane278GenConfig.deadBasis i) g = true
abbrev plane278GenIndicatorProperty (i : Fin 28) : Prop :=
  forall j : Fin 24, plane278GenConfig.occSys.occCoeff i j = if spanContainsCode (plane278GenConfig.sourceBasis i) (plane278GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
