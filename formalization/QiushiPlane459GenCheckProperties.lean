import QiushiPlane459GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane459GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 28, (plane459GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane459GenConfig.planeBasis (i.val ^^^ (plane459GenConfig.sectionCode j).val) = true
abbrev plane459GenDeadProperty (i : Fin 512) : Prop :=
  (plane459GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane459GenConfig.deadBasis (plane459GenConfig.deadCover i)) i.val = true
abbrev plane459GenSourceProperty (i : Fin 42) : Prop :=
  forall g : Nat, g ∈ plane459GenConfig.planeBasis -> spanContainsCode (plane459GenConfig.sourceBasis i) g = true
abbrev plane459GenDeadSourceProperty (i : Fin 35) : Prop :=
  forall g : Nat, g ∈ plane459GenConfig.planeBasis -> spanContainsCode (plane459GenConfig.deadBasis i) g = true
abbrev plane459GenIndicatorProperty (i : Fin 42) : Prop :=
  forall j : Fin 28, plane459GenConfig.occSys.occCoeff i j = if spanContainsCode (plane459GenConfig.sourceBasis i) (plane459GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
