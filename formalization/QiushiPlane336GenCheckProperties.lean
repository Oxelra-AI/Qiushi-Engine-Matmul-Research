import QiushiPlane336GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane336GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 18, (plane336GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane336GenConfig.planeBasis (i.val ^^^ (plane336GenConfig.sectionCode j).val) = true
abbrev plane336GenDeadProperty (i : Fin 512) : Prop :=
  (plane336GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane336GenConfig.deadBasis (plane336GenConfig.deadCover i)) i.val = true
abbrev plane336GenSourceProperty (i : Fin 34) : Prop :=
  forall g : Nat, g ∈ plane336GenConfig.planeBasis -> spanContainsCode (plane336GenConfig.sourceBasis i) g = true
abbrev plane336GenDeadSourceProperty (i : Fin 13) : Prop :=
  forall g : Nat, g ∈ plane336GenConfig.planeBasis -> spanContainsCode (plane336GenConfig.deadBasis i) g = true
abbrev plane336GenIndicatorProperty (i : Fin 34) : Prop :=
  forall j : Fin 18, plane336GenConfig.occSys.occCoeff i j = if spanContainsCode (plane336GenConfig.sourceBasis i) (plane336GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
