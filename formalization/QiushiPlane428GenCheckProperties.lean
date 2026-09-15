import QiushiPlane428GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane428GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 36, (plane428GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane428GenConfig.planeBasis (i.val ^^^ (plane428GenConfig.sectionCode j).val) = true
abbrev plane428GenDeadProperty (i : Fin 512) : Prop :=
  (plane428GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane428GenConfig.deadBasis (plane428GenConfig.deadCover i)) i.val = true
abbrev plane428GenSourceProperty (i : Fin 51) : Prop :=
  forall g : Nat, g ∈ plane428GenConfig.planeBasis -> spanContainsCode (plane428GenConfig.sourceBasis i) g = true
abbrev plane428GenDeadSourceProperty (i : Fin 19) : Prop :=
  forall g : Nat, g ∈ plane428GenConfig.planeBasis -> spanContainsCode (plane428GenConfig.deadBasis i) g = true
abbrev plane428GenIndicatorProperty (i : Fin 51) : Prop :=
  forall j : Fin 36, plane428GenConfig.occSys.occCoeff i j = if spanContainsCode (plane428GenConfig.sourceBasis i) (plane428GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
