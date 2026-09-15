import QiushiPlane298GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane298GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 13, (plane298GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane298GenConfig.planeBasis (i.val ^^^ (plane298GenConfig.sectionCode j).val) = true
abbrev plane298GenDeadProperty (i : Fin 512) : Prop :=
  (plane298GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane298GenConfig.deadBasis (plane298GenConfig.deadCover i)) i.val = true
abbrev plane298GenSourceProperty (i : Fin 28) : Prop :=
  forall g : Nat, g ∈ plane298GenConfig.planeBasis -> spanContainsCode (plane298GenConfig.sourceBasis i) g = true
abbrev plane298GenDeadSourceProperty (i : Fin 18) : Prop :=
  forall g : Nat, g ∈ plane298GenConfig.planeBasis -> spanContainsCode (plane298GenConfig.deadBasis i) g = true
abbrev plane298GenIndicatorProperty (i : Fin 28) : Prop :=
  forall j : Fin 13, plane298GenConfig.occSys.occCoeff i j = if spanContainsCode (plane298GenConfig.sourceBasis i) (plane298GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
