import QiushiPlane488GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane488GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 41, (plane488GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane488GenConfig.planeBasis (i.val ^^^ (plane488GenConfig.sectionCode j).val) = true
abbrev plane488GenDeadProperty (i : Fin 512) : Prop :=
  (plane488GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane488GenConfig.deadBasis (plane488GenConfig.deadCover i)) i.val = true
abbrev plane488GenSourceProperty (i : Fin 413) : Prop :=
  forall g : Nat, g ∈ plane488GenConfig.planeBasis -> spanContainsCode (plane488GenConfig.sourceBasis i) g = true
abbrev plane488GenDeadSourceProperty (i : Fin 86) : Prop :=
  forall g : Nat, g ∈ plane488GenConfig.planeBasis -> spanContainsCode (plane488GenConfig.deadBasis i) g = true
abbrev plane488GenIndicatorProperty (i : Fin 413) : Prop :=
  forall j : Fin 41, plane488GenConfig.occSys.occCoeff i j = if spanContainsCode (plane488GenConfig.sourceBasis i) (plane488GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
