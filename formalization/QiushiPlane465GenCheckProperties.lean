import QiushiPlane465GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane465GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 57, (plane465GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane465GenConfig.planeBasis (i.val ^^^ (plane465GenConfig.sectionCode j).val) = true
abbrev plane465GenDeadProperty (i : Fin 512) : Prop :=
  (plane465GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane465GenConfig.deadBasis (plane465GenConfig.deadCover i)) i.val = true
abbrev plane465GenSourceProperty (i : Fin 88) : Prop :=
  forall g : Nat, g ∈ plane465GenConfig.planeBasis -> spanContainsCode (plane465GenConfig.sourceBasis i) g = true
abbrev plane465GenDeadSourceProperty (i : Fin 6) : Prop :=
  forall g : Nat, g ∈ plane465GenConfig.planeBasis -> spanContainsCode (plane465GenConfig.deadBasis i) g = true
abbrev plane465GenIndicatorProperty (i : Fin 88) : Prop :=
  forall j : Fin 57, plane465GenConfig.occSys.occCoeff i j = if spanContainsCode (plane465GenConfig.sourceBasis i) (plane465GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
