import QiushiPlane464GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane464GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 50, (plane464GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane464GenConfig.planeBasis (i.val ^^^ (plane464GenConfig.sectionCode j).val) = true
abbrev plane464GenDeadProperty (i : Fin 512) : Prop :=
  (plane464GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane464GenConfig.deadBasis (plane464GenConfig.deadCover i)) i.val = true
abbrev plane464GenSourceProperty (i : Fin 202) : Prop :=
  forall g : Nat, g ∈ plane464GenConfig.planeBasis -> spanContainsCode (plane464GenConfig.sourceBasis i) g = true
abbrev plane464GenDeadSourceProperty (i : Fin 13) : Prop :=
  forall g : Nat, g ∈ plane464GenConfig.planeBasis -> spanContainsCode (plane464GenConfig.deadBasis i) g = true
abbrev plane464GenIndicatorProperty (i : Fin 202) : Prop :=
  forall j : Fin 50, plane464GenConfig.occSys.occCoeff i j = if spanContainsCode (plane464GenConfig.sourceBasis i) (plane464GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
