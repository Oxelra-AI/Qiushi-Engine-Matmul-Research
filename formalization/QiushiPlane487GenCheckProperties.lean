import QiushiPlane487GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane487GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 48, (plane487GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane487GenConfig.planeBasis (i.val ^^^ (plane487GenConfig.sectionCode j).val) = true
abbrev plane487GenDeadProperty (i : Fin 512) : Prop :=
  (plane487GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane487GenConfig.deadBasis (plane487GenConfig.deadCover i)) i.val = true
abbrev plane487GenSourceProperty (i : Fin 668) : Prop :=
  forall g : Nat, g ∈ plane487GenConfig.planeBasis -> spanContainsCode (plane487GenConfig.sourceBasis i) g = true
abbrev plane487GenDeadSourceProperty (i : Fin 79) : Prop :=
  forall g : Nat, g ∈ plane487GenConfig.planeBasis -> spanContainsCode (plane487GenConfig.deadBasis i) g = true
abbrev plane487GenIndicatorProperty (i : Fin 668) : Prop :=
  forall j : Fin 48, plane487GenConfig.occSys.occCoeff i j = if spanContainsCode (plane487GenConfig.sourceBasis i) (plane487GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
