import QiushiPlane447GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane447GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 13, (plane447GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane447GenConfig.planeBasis (i.val ^^^ (plane447GenConfig.sectionCode j).val) = true
abbrev plane447GenDeadProperty (i : Fin 512) : Prop :=
  (plane447GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane447GenConfig.deadBasis (plane447GenConfig.deadCover i)) i.val = true
abbrev plane447GenSourceProperty (i : Fin 55) : Prop :=
  forall g : Nat, g ∈ plane447GenConfig.planeBasis -> spanContainsCode (plane447GenConfig.sourceBasis i) g = true
abbrev plane447GenDeadSourceProperty (i : Fin 50) : Prop :=
  forall g : Nat, g ∈ plane447GenConfig.planeBasis -> spanContainsCode (plane447GenConfig.deadBasis i) g = true
abbrev plane447GenIndicatorProperty (i : Fin 55) : Prop :=
  forall j : Fin 13, plane447GenConfig.occSys.occCoeff i j = if spanContainsCode (plane447GenConfig.sourceBasis i) (plane447GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
