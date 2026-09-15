import QiushiPlane470GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane470GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 63, (plane470GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane470GenConfig.planeBasis (i.val ^^^ (plane470GenConfig.sectionCode j).val) = true
abbrev plane470GenDeadProperty (i : Fin 512) : Prop :=
  (plane470GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane470GenConfig.deadBasis (plane470GenConfig.deadCover i)) i.val = true
abbrev plane470GenSourceProperty (i : Fin 232) : Prop :=
  forall g : Nat, g ∈ plane470GenConfig.planeBasis -> spanContainsCode (plane470GenConfig.sourceBasis i) g = true
abbrev plane470GenDeadSourceProperty (i : Fin 1) : Prop :=
  forall g : Nat, g ∈ plane470GenConfig.planeBasis -> spanContainsCode (plane470GenConfig.deadBasis i) g = true
abbrev plane470GenIndicatorProperty (i : Fin 232) : Prop :=
  forall j : Fin 63, plane470GenConfig.occSys.occCoeff i j = if spanContainsCode (plane470GenConfig.sourceBasis i) (plane470GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
