import QiushiPlane474GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane474GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 60, (plane474GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane474GenConfig.planeBasis (i.val ^^^ (plane474GenConfig.sectionCode j).val) = true
abbrev plane474GenDeadProperty (i : Fin 512) : Prop :=
  (plane474GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane474GenConfig.deadBasis (plane474GenConfig.deadCover i)) i.val = true
abbrev plane474GenSourceProperty (i : Fin 146) : Prop :=
  forall g : Nat, g ∈ plane474GenConfig.planeBasis -> spanContainsCode (plane474GenConfig.sourceBasis i) g = true
abbrev plane474GenDeadSourceProperty (i : Fin 3) : Prop :=
  forall g : Nat, g ∈ plane474GenConfig.planeBasis -> spanContainsCode (plane474GenConfig.deadBasis i) g = true
abbrev plane474GenIndicatorProperty (i : Fin 146) : Prop :=
  forall j : Fin 60, plane474GenConfig.occSys.occCoeff i j = if spanContainsCode (plane474GenConfig.sourceBasis i) (plane474GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
