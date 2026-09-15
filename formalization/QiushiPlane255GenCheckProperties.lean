import QiushiPlane255GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane255GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 14, (plane255GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane255GenConfig.planeBasis (i.val ^^^ (plane255GenConfig.sectionCode j).val) = true
abbrev plane255GenDeadProperty (i : Fin 512) : Prop :=
  (plane255GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane255GenConfig.deadBasis (plane255GenConfig.deadCover i)) i.val = true
abbrev plane255GenSourceProperty (i : Fin 25) : Prop :=
  forall g : Nat, g ∈ plane255GenConfig.planeBasis -> spanContainsCode (plane255GenConfig.sourceBasis i) g = true
abbrev plane255GenDeadSourceProperty (i : Fin 17) : Prop :=
  forall g : Nat, g ∈ plane255GenConfig.planeBasis -> spanContainsCode (plane255GenConfig.deadBasis i) g = true
abbrev plane255GenIndicatorProperty (i : Fin 25) : Prop :=
  forall j : Fin 14, plane255GenConfig.occSys.occCoeff i j = if spanContainsCode (plane255GenConfig.sourceBasis i) (plane255GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
