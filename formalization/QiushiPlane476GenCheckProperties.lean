import QiushiPlane476GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane476GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 50, (plane476GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane476GenConfig.planeBasis (i.val ^^^ (plane476GenConfig.sectionCode j).val) = true
abbrev plane476GenDeadProperty (i : Fin 512) : Prop :=
  (plane476GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane476GenConfig.deadBasis (plane476GenConfig.deadCover i)) i.val = true
abbrev plane476GenSourceProperty (i : Fin 113) : Prop :=
  forall g : Nat, g ∈ plane476GenConfig.planeBasis -> spanContainsCode (plane476GenConfig.sourceBasis i) g = true
abbrev plane476GenDeadSourceProperty (i : Fin 13) : Prop :=
  forall g : Nat, g ∈ plane476GenConfig.planeBasis -> spanContainsCode (plane476GenConfig.deadBasis i) g = true
abbrev plane476GenIndicatorProperty (i : Fin 113) : Prop :=
  forall j : Fin 50, plane476GenConfig.occSys.occCoeff i j = if spanContainsCode (plane476GenConfig.sourceBasis i) (plane476GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
