import QiushiPlane276GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane276GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 17, (plane276GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane276GenConfig.planeBasis (i.val ^^^ (plane276GenConfig.sectionCode j).val) = true
abbrev plane276GenDeadProperty (i : Fin 512) : Prop :=
  (plane276GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane276GenConfig.deadBasis (plane276GenConfig.deadCover i)) i.val = true
abbrev plane276GenSourceProperty (i : Fin 37) : Prop :=
  forall g : Nat, g ∈ plane276GenConfig.planeBasis -> spanContainsCode (plane276GenConfig.sourceBasis i) g = true
abbrev plane276GenDeadSourceProperty (i : Fin 17) : Prop :=
  forall g : Nat, g ∈ plane276GenConfig.planeBasis -> spanContainsCode (plane276GenConfig.deadBasis i) g = true
abbrev plane276GenIndicatorProperty (i : Fin 37) : Prop :=
  forall j : Fin 17, plane276GenConfig.occSys.occCoeff i j = if spanContainsCode (plane276GenConfig.sourceBasis i) (plane276GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
