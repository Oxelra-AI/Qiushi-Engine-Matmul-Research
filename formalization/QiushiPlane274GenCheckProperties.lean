import QiushiPlane274GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane274GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 21, (plane274GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane274GenConfig.planeBasis (i.val ^^^ (plane274GenConfig.sectionCode j).val) = true
abbrev plane274GenDeadProperty (i : Fin 512) : Prop :=
  (plane274GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane274GenConfig.deadBasis (plane274GenConfig.deadCover i)) i.val = true
abbrev plane274GenSourceProperty (i : Fin 29) : Prop :=
  forall g : Nat, g ∈ plane274GenConfig.planeBasis -> spanContainsCode (plane274GenConfig.sourceBasis i) g = true
abbrev plane274GenDeadSourceProperty (i : Fin 10) : Prop :=
  forall g : Nat, g ∈ plane274GenConfig.planeBasis -> spanContainsCode (plane274GenConfig.deadBasis i) g = true
abbrev plane274GenIndicatorProperty (i : Fin 29) : Prop :=
  forall j : Fin 21, plane274GenConfig.occSys.occCoeff i j = if spanContainsCode (plane274GenConfig.sourceBasis i) (plane274GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
