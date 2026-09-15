import QiushiPlane439GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane439GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 13, (plane439GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane439GenConfig.planeBasis (i.val ^^^ (plane439GenConfig.sectionCode j).val) = true
abbrev plane439GenDeadProperty (i : Fin 512) : Prop :=
  (plane439GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane439GenConfig.deadBasis (plane439GenConfig.deadCover i)) i.val = true
abbrev plane439GenSourceProperty (i : Fin 59) : Prop :=
  forall g : Nat, g ∈ plane439GenConfig.planeBasis -> spanContainsCode (plane439GenConfig.sourceBasis i) g = true
abbrev plane439GenDeadSourceProperty (i : Fin 48) : Prop :=
  forall g : Nat, g ∈ plane439GenConfig.planeBasis -> spanContainsCode (plane439GenConfig.deadBasis i) g = true
abbrev plane439GenIndicatorProperty (i : Fin 59) : Prop :=
  forall j : Fin 13, plane439GenConfig.occSys.occCoeff i j = if spanContainsCode (plane439GenConfig.sourceBasis i) (plane439GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
