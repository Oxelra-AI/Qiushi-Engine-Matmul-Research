import QiushiPlane484GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane484GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 43, (plane484GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane484GenConfig.planeBasis (i.val ^^^ (plane484GenConfig.sectionCode j).val) = true
abbrev plane484GenDeadProperty (i : Fin 512) : Prop :=
  (plane484GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane484GenConfig.deadBasis (plane484GenConfig.deadCover i)) i.val = true
abbrev plane484GenSourceProperty (i : Fin 1665) : Prop :=
  forall g : Nat, g ∈ plane484GenConfig.planeBasis -> spanContainsCode (plane484GenConfig.sourceBasis i) g = true
abbrev plane484GenDeadSourceProperty (i : Fin 84) : Prop :=
  forall g : Nat, g ∈ plane484GenConfig.planeBasis -> spanContainsCode (plane484GenConfig.deadBasis i) g = true
abbrev plane484GenIndicatorProperty (i : Fin 1665) : Prop :=
  forall j : Fin 43, plane484GenConfig.occSys.occCoeff i j = if spanContainsCode (plane484GenConfig.sourceBasis i) (plane484GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
