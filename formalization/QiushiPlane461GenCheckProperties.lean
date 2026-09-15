import QiushiPlane461GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane461GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 62, (plane461GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane461GenConfig.planeBasis (i.val ^^^ (plane461GenConfig.sectionCode j).val) = true
abbrev plane461GenDeadProperty (i : Fin 512) : Prop :=
  (plane461GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane461GenConfig.deadBasis (plane461GenConfig.deadCover i)) i.val = true
abbrev plane461GenSourceProperty (i : Fin 151) : Prop :=
  forall g : Nat, g ∈ plane461GenConfig.planeBasis -> spanContainsCode (plane461GenConfig.sourceBasis i) g = true
abbrev plane461GenDeadSourceProperty (i : Fin 1) : Prop :=
  forall g : Nat, g ∈ plane461GenConfig.planeBasis -> spanContainsCode (plane461GenConfig.deadBasis i) g = true
abbrev plane461GenIndicatorProperty (i : Fin 151) : Prop :=
  forall j : Fin 62, plane461GenConfig.occSys.occCoeff i j = if spanContainsCode (plane461GenConfig.sourceBasis i) (plane461GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
