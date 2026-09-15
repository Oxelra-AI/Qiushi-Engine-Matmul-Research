import QiushiPlane427GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane427GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 50, (plane427GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane427GenConfig.planeBasis (i.val ^^^ (plane427GenConfig.sectionCode j).val) = true
abbrev plane427GenDeadProperty (i : Fin 512) : Prop :=
  (plane427GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane427GenConfig.deadBasis (plane427GenConfig.deadCover i)) i.val = true
abbrev plane427GenSourceProperty (i : Fin 237) : Prop :=
  forall g : Nat, g ∈ plane427GenConfig.planeBasis -> spanContainsCode (plane427GenConfig.sourceBasis i) g = true
abbrev plane427GenDeadSourceProperty (i : Fin 6) : Prop :=
  forall g : Nat, g ∈ plane427GenConfig.planeBasis -> spanContainsCode (plane427GenConfig.deadBasis i) g = true
abbrev plane427GenIndicatorProperty (i : Fin 237) : Prop :=
  forall j : Fin 50, plane427GenConfig.occSys.occCoeff i j = if spanContainsCode (plane427GenConfig.sourceBasis i) (plane427GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
