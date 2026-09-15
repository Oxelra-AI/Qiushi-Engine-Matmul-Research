import QiushiPlane483GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane483GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 36, (plane483GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane483GenConfig.planeBasis (i.val ^^^ (plane483GenConfig.sectionCode j).val) = true
abbrev plane483GenDeadProperty (i : Fin 512) : Prop :=
  (plane483GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane483GenConfig.deadBasis (plane483GenConfig.deadCover i)) i.val = true
abbrev plane483GenSourceProperty (i : Fin 112) : Prop :=
  forall g : Nat, g ∈ plane483GenConfig.planeBasis -> spanContainsCode (plane483GenConfig.sourceBasis i) g = true
abbrev plane483GenDeadSourceProperty (i : Fin 76) : Prop :=
  forall g : Nat, g ∈ plane483GenConfig.planeBasis -> spanContainsCode (plane483GenConfig.deadBasis i) g = true
abbrev plane483GenIndicatorProperty (i : Fin 112) : Prop :=
  forall j : Fin 36, plane483GenConfig.occSys.occCoeff i j = if spanContainsCode (plane483GenConfig.sourceBasis i) (plane483GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
