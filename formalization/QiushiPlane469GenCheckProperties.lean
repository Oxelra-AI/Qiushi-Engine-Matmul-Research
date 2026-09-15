import QiushiPlane469GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane469GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 60, (plane469GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane469GenConfig.planeBasis (i.val ^^^ (plane469GenConfig.sectionCode j).val) = true
abbrev plane469GenDeadProperty (i : Fin 512) : Prop :=
  (plane469GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane469GenConfig.deadBasis (plane469GenConfig.deadCover i)) i.val = true
abbrev plane469GenSourceProperty (i : Fin 217) : Prop :=
  forall g : Nat, g ∈ plane469GenConfig.planeBasis -> spanContainsCode (plane469GenConfig.sourceBasis i) g = true
abbrev plane469GenDeadSourceProperty (i : Fin 3) : Prop :=
  forall g : Nat, g ∈ plane469GenConfig.planeBasis -> spanContainsCode (plane469GenConfig.deadBasis i) g = true
abbrev plane469GenIndicatorProperty (i : Fin 217) : Prop :=
  forall j : Fin 60, plane469GenConfig.occSys.occCoeff i j = if spanContainsCode (plane469GenConfig.sourceBasis i) (plane469GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
