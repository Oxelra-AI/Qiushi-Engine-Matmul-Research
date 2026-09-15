import QiushiPlane467GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane467GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 59, (plane467GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane467GenConfig.planeBasis (i.val ^^^ (plane467GenConfig.sectionCode j).val) = true
abbrev plane467GenDeadProperty (i : Fin 512) : Prop :=
  (plane467GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane467GenConfig.deadBasis (plane467GenConfig.deadCover i)) i.val = true
abbrev plane467GenSourceProperty (i : Fin 84) : Prop :=
  forall g : Nat, g ∈ plane467GenConfig.planeBasis -> spanContainsCode (plane467GenConfig.sourceBasis i) g = true
abbrev plane467GenDeadSourceProperty (i : Fin 4) : Prop :=
  forall g : Nat, g ∈ plane467GenConfig.planeBasis -> spanContainsCode (plane467GenConfig.deadBasis i) g = true
abbrev plane467GenIndicatorProperty (i : Fin 84) : Prop :=
  forall j : Fin 59, plane467GenConfig.occSys.occCoeff i j = if spanContainsCode (plane467GenConfig.sourceBasis i) (plane467GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
