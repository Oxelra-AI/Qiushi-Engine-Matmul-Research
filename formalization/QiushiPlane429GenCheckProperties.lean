import QiushiPlane429GenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane429GenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 61, (plane429GenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane429GenConfig.planeBasis (i.val ^^^ (plane429GenConfig.sectionCode j).val) = true
abbrev plane429GenDeadProperty (i : Fin 512) : Prop :=
  (plane429GenConfig.classifyCode i).val = 0 -> spanContainsCode (plane429GenConfig.deadBasis (plane429GenConfig.deadCover i)) i.val = true
abbrev plane429GenSourceProperty (i : Fin 55) : Prop :=
  forall g : Nat, g ∈ plane429GenConfig.planeBasis -> spanContainsCode (plane429GenConfig.sourceBasis i) g = true
abbrev plane429GenDeadSourceProperty (i : Fin 2) : Prop :=
  forall g : Nat, g ∈ plane429GenConfig.planeBasis -> spanContainsCode (plane429GenConfig.deadBasis i) g = true
abbrev plane429GenIndicatorProperty (i : Fin 55) : Prop :=
  forall j : Fin 61, plane429GenConfig.occSys.occCoeff i j = if spanContainsCode (plane429GenConfig.sourceBasis i) (plane429GenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
