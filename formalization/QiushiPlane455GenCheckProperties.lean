import QiushiPlane455GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane455GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 48, (plane455GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane455GenConfig.planeBasis (i.val ^^^ (plane455GenConfig.sectionCode j).val) = true
abbrev plane455GenDeadProperty (i : Fin 512) : Prop :=
  (plane455GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane455GenConfig.deadBasis (plane455GenConfig.deadCover i)) i.val = true
abbrev plane455GenSourceProperty (i : Fin 124) : Prop :=
  forall g : Nat, g ∈ plane455GenConfig.planeBasis -> spanContainsCode (plane455GenConfig.sourceBasis i) g = true
abbrev plane455GenDeadSourceProperty (i : Fin 15) : Prop :=
  forall g : Nat, g ∈ plane455GenConfig.planeBasis -> spanContainsCode (plane455GenConfig.deadBasis i) g = true
abbrev plane455GenIndicatorProperty (i : Fin 124) : Prop :=
  forall j : Fin 48, plane455GenConfig.occSys.occCoeff i j = if spanContainsCode (plane455GenConfig.sourceBasis i) (plane455GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
