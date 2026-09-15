import QiushiPlane453GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane453GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 50, (plane453GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane453GenConfig.planeBasis (i.val ^^^ (plane453GenConfig.sectionCode j).val) = true
abbrev plane453GenDeadProperty (i : Fin 512) : Prop :=
  (plane453GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane453GenConfig.deadBasis (plane453GenConfig.deadCover i)) i.val = true
abbrev plane453GenSourceProperty (i : Fin 210) : Prop :=
  forall g : Nat, g ∈ plane453GenConfig.planeBasis -> spanContainsCode (plane453GenConfig.sourceBasis i) g = true
abbrev plane453GenDeadSourceProperty (i : Fin 13) : Prop :=
  forall g : Nat, g ∈ plane453GenConfig.planeBasis -> spanContainsCode (plane453GenConfig.deadBasis i) g = true
abbrev plane453GenIndicatorProperty (i : Fin 210) : Prop :=
  forall j : Fin 50, plane453GenConfig.occSys.occCoeff i j = if spanContainsCode (plane453GenConfig.sourceBasis i) (plane453GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
