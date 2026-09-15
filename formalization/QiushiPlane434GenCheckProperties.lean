import QiushiPlane434GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane434GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 37, (plane434GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane434GenConfig.planeBasis (i.val ^^^ (plane434GenConfig.sectionCode j).val) = true
abbrev plane434GenDeadProperty (i : Fin 512) : Prop :=
  (plane434GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane434GenConfig.deadBasis (plane434GenConfig.deadCover i)) i.val = true
abbrev plane434GenSourceProperty (i : Fin 63) : Prop :=
  forall g : Nat, g ∈ plane434GenConfig.planeBasis -> spanContainsCode (plane434GenConfig.sourceBasis i) g = true
abbrev plane434GenDeadSourceProperty (i : Fin 26) : Prop :=
  forall g : Nat, g ∈ plane434GenConfig.planeBasis -> spanContainsCode (plane434GenConfig.deadBasis i) g = true
abbrev plane434GenIndicatorProperty (i : Fin 63) : Prop :=
  forall j : Fin 37, plane434GenConfig.occSys.occCoeff i j = if spanContainsCode (plane434GenConfig.sourceBasis i) (plane434GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
