import QiushiPlane463GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane463GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 63, (plane463GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane463GenConfig.planeBasis (i.val ^^^ (plane463GenConfig.sectionCode j).val) = true
abbrev plane463GenDeadProperty (i : Fin 512) : Prop :=
  (plane463GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane463GenConfig.deadBasis (plane463GenConfig.deadCover i)) i.val = true
abbrev plane463GenSourceProperty (i : Fin 278) : Prop :=
  forall g : Nat, g ∈ plane463GenConfig.planeBasis -> spanContainsCode (plane463GenConfig.sourceBasis i) g = true
abbrev plane463GenDeadSourceProperty (i : Fin 1) : Prop :=
  forall g : Nat, g ∈ plane463GenConfig.planeBasis -> spanContainsCode (plane463GenConfig.deadBasis i) g = true
abbrev plane463GenIndicatorProperty (i : Fin 278) : Prop :=
  forall j : Fin 63, plane463GenConfig.occSys.occCoeff i j = if spanContainsCode (plane463GenConfig.sourceBasis i) (plane463GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
