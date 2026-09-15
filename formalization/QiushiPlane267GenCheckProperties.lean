import QiushiPlane267GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane267GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 20, (plane267GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane267GenConfig.planeBasis (i.val ^^^ (plane267GenConfig.sectionCode j).val) = true
abbrev plane267GenDeadProperty (i : Fin 512) : Prop :=
  (plane267GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane267GenConfig.deadBasis (plane267GenConfig.deadCover i)) i.val = true
abbrev plane267GenSourceProperty (i : Fin 33) : Prop :=
  forall g : Nat, g ∈ plane267GenConfig.planeBasis -> spanContainsCode (plane267GenConfig.sourceBasis i) g = true
abbrev plane267GenDeadSourceProperty (i : Fin 11) : Prop :=
  forall g : Nat, g ∈ plane267GenConfig.planeBasis -> spanContainsCode (plane267GenConfig.deadBasis i) g = true
abbrev plane267GenIndicatorProperty (i : Fin 33) : Prop :=
  forall j : Fin 20, plane267GenConfig.occSys.occCoeff i j = if spanContainsCode (plane267GenConfig.sourceBasis i) (plane267GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
