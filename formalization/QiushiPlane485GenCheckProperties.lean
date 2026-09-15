import QiushiPlane485GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane485GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 41, (plane485GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane485GenConfig.planeBasis (i.val ^^^ (plane485GenConfig.sectionCode j).val) = true
abbrev plane485GenDeadProperty (i : Fin 512) : Prop :=
  (plane485GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane485GenConfig.deadBasis (plane485GenConfig.deadCover i)) i.val = true
abbrev plane485GenSourceProperty (i : Fin 421) : Prop :=
  forall g : Nat, g ∈ plane485GenConfig.planeBasis -> spanContainsCode (plane485GenConfig.sourceBasis i) g = true
abbrev plane485GenDeadSourceProperty (i : Fin 86) : Prop :=
  forall g : Nat, g ∈ plane485GenConfig.planeBasis -> spanContainsCode (plane485GenConfig.deadBasis i) g = true
abbrev plane485GenIndicatorProperty (i : Fin 421) : Prop :=
  forall j : Fin 41, plane485GenConfig.occSys.occCoeff i j = if spanContainsCode (plane485GenConfig.sourceBasis i) (plane485GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
