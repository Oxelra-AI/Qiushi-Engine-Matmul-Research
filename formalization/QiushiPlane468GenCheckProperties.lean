import QiushiPlane468GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane468GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 62, (plane468GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane468GenConfig.planeBasis (i.val ^^^ (plane468GenConfig.sectionCode j).val) = true
abbrev plane468GenDeadProperty (i : Fin 512) : Prop :=
  (plane468GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane468GenConfig.deadBasis (plane468GenConfig.deadCover i)) i.val = true
abbrev plane468GenSourceProperty (i : Fin 253) : Prop :=
  forall g : Nat, g ∈ plane468GenConfig.planeBasis -> spanContainsCode (plane468GenConfig.sourceBasis i) g = true
abbrev plane468GenDeadSourceProperty (i : Fin 1) : Prop :=
  forall g : Nat, g ∈ plane468GenConfig.planeBasis -> spanContainsCode (plane468GenConfig.deadBasis i) g = true
abbrev plane468GenIndicatorProperty (i : Fin 253) : Prop :=
  forall j : Fin 62, plane468GenConfig.occSys.occCoeff i j = if spanContainsCode (plane468GenConfig.sourceBasis i) (plane468GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
