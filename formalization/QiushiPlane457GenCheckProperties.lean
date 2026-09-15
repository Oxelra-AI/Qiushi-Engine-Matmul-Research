import QiushiPlane457GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane457GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 49, (plane457GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane457GenConfig.planeBasis (i.val ^^^ (plane457GenConfig.sectionCode j).val) = true
abbrev plane457GenDeadProperty (i : Fin 512) : Prop :=
  (plane457GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane457GenConfig.deadBasis (plane457GenConfig.deadCover i)) i.val = true
abbrev plane457GenSourceProperty (i : Fin 178) : Prop :=
  forall g : Nat, g ∈ plane457GenConfig.planeBasis -> spanContainsCode (plane457GenConfig.sourceBasis i) g = true
abbrev plane457GenDeadSourceProperty (i : Fin 14) : Prop :=
  forall g : Nat, g ∈ plane457GenConfig.planeBasis -> spanContainsCode (plane457GenConfig.deadBasis i) g = true
abbrev plane457GenIndicatorProperty (i : Fin 178) : Prop :=
  forall j : Fin 49, plane457GenConfig.occSys.occCoeff i j = if spanContainsCode (plane457GenConfig.sourceBasis i) (plane457GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
