import QiushiPlane462GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane462GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 62, (plane462GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane462GenConfig.planeBasis (i.val ^^^ (plane462GenConfig.sectionCode j).val) = true
abbrev plane462GenDeadProperty (i : Fin 512) : Prop :=
  (plane462GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane462GenConfig.deadBasis (plane462GenConfig.deadCover i)) i.val = true
abbrev plane462GenSourceProperty (i : Fin 294) : Prop :=
  forall g : Nat, g ∈ plane462GenConfig.planeBasis -> spanContainsCode (plane462GenConfig.sourceBasis i) g = true
abbrev plane462GenDeadSourceProperty (i : Fin 1) : Prop :=
  forall g : Nat, g ∈ plane462GenConfig.planeBasis -> spanContainsCode (plane462GenConfig.deadBasis i) g = true
abbrev plane462GenIndicatorProperty (i : Fin 294) : Prop :=
  forall j : Fin 62, plane462GenConfig.occSys.occCoeff i j = if spanContainsCode (plane462GenConfig.sourceBasis i) (plane462GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
