import QiushiGlobalOrbitUnused395Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane395UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 11, (plane395UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane395UnusedGenConfig.planeBasis (i.val ^^^ (plane395UnusedGenConfig.sectionCode j).val) = true
abbrev plane395UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane395UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane395UnusedGenConfig.deadBasis (plane395UnusedGenConfig.deadCover i)) i.val = true
abbrev plane395UnusedGenSourceProperty (i : Fin 28) : Prop :=
  forall g : Nat, g ∈ plane395UnusedGenConfig.planeBasis -> spanContainsCode (plane395UnusedGenConfig.sourceBasis i) g = true
abbrev plane395UnusedGenDeadSourceProperty (i : Fin 21) : Prop :=
  forall g : Nat, g ∈ plane395UnusedGenConfig.planeBasis -> spanContainsCode (plane395UnusedGenConfig.deadBasis i) g = true
abbrev plane395UnusedGenIndicatorProperty (i : Fin 28) : Prop :=
  forall j : Fin 11, plane395UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane395UnusedGenConfig.sourceBasis i) (plane395UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
