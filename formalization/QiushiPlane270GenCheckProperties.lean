import QiushiPlane270GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane270GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 11, (plane270GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane270GenConfig.planeBasis (i.val ^^^ (plane270GenConfig.sectionCode j).val) = true
abbrev plane270GenDeadProperty (i : Fin 512) : Prop :=
  (plane270GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane270GenConfig.deadBasis (plane270GenConfig.deadCover i)) i.val = true
abbrev plane270GenSourceProperty (i : Fin 22) : Prop :=
  forall g : Nat, g ∈ plane270GenConfig.planeBasis -> spanContainsCode (plane270GenConfig.sourceBasis i) g = true
abbrev plane270GenDeadSourceProperty (i : Fin 20) : Prop :=
  forall g : Nat, g ∈ plane270GenConfig.planeBasis -> spanContainsCode (plane270GenConfig.deadBasis i) g = true
abbrev plane270GenIndicatorProperty (i : Fin 22) : Prop :=
  forall j : Fin 11, plane270GenConfig.occSys.occCoeff i j = if spanContainsCode (plane270GenConfig.sourceBasis i) (plane270GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
