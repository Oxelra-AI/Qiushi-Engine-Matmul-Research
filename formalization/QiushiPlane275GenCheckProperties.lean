import QiushiPlane275GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane275GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 9, (plane275GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane275GenConfig.planeBasis (i.val ^^^ (plane275GenConfig.sectionCode j).val) = true
abbrev plane275GenDeadProperty (i : Fin 512) : Prop :=
  (plane275GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane275GenConfig.deadBasis (plane275GenConfig.deadCover i)) i.val = true
abbrev plane275GenSourceProperty (i : Fin 29) : Prop :=
  forall g : Nat, g ∈ plane275GenConfig.planeBasis -> spanContainsCode (plane275GenConfig.sourceBasis i) g = true
abbrev plane275GenDeadSourceProperty (i : Fin 22) : Prop :=
  forall g : Nat, g ∈ plane275GenConfig.planeBasis -> spanContainsCode (plane275GenConfig.deadBasis i) g = true
abbrev plane275GenIndicatorProperty (i : Fin 29) : Prop :=
  forall j : Fin 9, plane275GenConfig.occSys.occCoeff i j = if spanContainsCode (plane275GenConfig.sourceBasis i) (plane275GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
