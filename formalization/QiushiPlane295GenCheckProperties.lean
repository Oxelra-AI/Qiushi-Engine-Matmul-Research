import QiushiPlane295GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane295GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 24, (plane295GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane295GenConfig.planeBasis (i.val ^^^ (plane295GenConfig.sectionCode j).val) = true
abbrev plane295GenDeadProperty (i : Fin 512) : Prop :=
  (plane295GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane295GenConfig.deadBasis (plane295GenConfig.deadCover i)) i.val = true
abbrev plane295GenSourceProperty (i : Fin 46) : Prop :=
  forall g : Nat, g ∈ plane295GenConfig.planeBasis -> spanContainsCode (plane295GenConfig.sourceBasis i) g = true
abbrev plane295GenDeadSourceProperty (i : Fin 7) : Prop :=
  forall g : Nat, g ∈ plane295GenConfig.planeBasis -> spanContainsCode (plane295GenConfig.deadBasis i) g = true
abbrev plane295GenIndicatorProperty (i : Fin 46) : Prop :=
  forall j : Fin 24, plane295GenConfig.occSys.occCoeff i j = if spanContainsCode (plane295GenConfig.sourceBasis i) (plane295GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
