import QiushiPlane473GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane473GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 59, (plane473GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane473GenConfig.planeBasis (i.val ^^^ (plane473GenConfig.sectionCode j).val) = true
abbrev plane473GenDeadProperty (i : Fin 512) : Prop :=
  (plane473GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane473GenConfig.deadBasis (plane473GenConfig.deadCover i)) i.val = true
abbrev plane473GenSourceProperty (i : Fin 153) : Prop :=
  forall g : Nat, g ∈ plane473GenConfig.planeBasis -> spanContainsCode (plane473GenConfig.sourceBasis i) g = true
abbrev plane473GenDeadSourceProperty (i : Fin 4) : Prop :=
  forall g : Nat, g ∈ plane473GenConfig.planeBasis -> spanContainsCode (plane473GenConfig.deadBasis i) g = true
abbrev plane473GenIndicatorProperty (i : Fin 153) : Prop :=
  forall j : Fin 59, plane473GenConfig.occSys.occCoeff i j = if spanContainsCode (plane473GenConfig.sourceBasis i) (plane473GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
