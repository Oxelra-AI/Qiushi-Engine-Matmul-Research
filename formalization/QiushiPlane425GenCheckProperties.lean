import QiushiPlane425GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane425GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 58, (plane425GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane425GenConfig.planeBasis (i.val ^^^ (plane425GenConfig.sectionCode j).val) = true
abbrev plane425GenDeadProperty (i : Fin 512) : Prop :=
  (plane425GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane425GenConfig.deadBasis (plane425GenConfig.deadCover i)) i.val = true
abbrev plane425GenSourceProperty (i : Fin 202) : Prop :=
  forall g : Nat, g ∈ plane425GenConfig.planeBasis -> spanContainsCode (plane425GenConfig.sourceBasis i) g = true
abbrev plane425GenDeadSourceProperty (i : Fin 5) : Prop :=
  forall g : Nat, g ∈ plane425GenConfig.planeBasis -> spanContainsCode (plane425GenConfig.deadBasis i) g = true
abbrev plane425GenIndicatorProperty (i : Fin 202) : Prop :=
  forall j : Fin 58, plane425GenConfig.occSys.occCoeff i j = if spanContainsCode (plane425GenConfig.sourceBasis i) (plane425GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
