import QiushiPlane448GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane448GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 22, (plane448GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane448GenConfig.planeBasis (i.val ^^^ (plane448GenConfig.sectionCode j).val) = true
abbrev plane448GenDeadProperty (i : Fin 512) : Prop :=
  (plane448GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane448GenConfig.deadBasis (plane448GenConfig.deadCover i)) i.val = true
abbrev plane448GenSourceProperty (i : Fin 56) : Prop :=
  forall g : Nat, g ∈ plane448GenConfig.planeBasis -> spanContainsCode (plane448GenConfig.sourceBasis i) g = true
abbrev plane448GenDeadSourceProperty (i : Fin 38) : Prop :=
  forall g : Nat, g ∈ plane448GenConfig.planeBasis -> spanContainsCode (plane448GenConfig.deadBasis i) g = true
abbrev plane448GenIndicatorProperty (i : Fin 56) : Prop :=
  forall j : Fin 22, plane448GenConfig.occSys.occCoeff i j = if spanContainsCode (plane448GenConfig.sourceBasis i) (plane448GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
