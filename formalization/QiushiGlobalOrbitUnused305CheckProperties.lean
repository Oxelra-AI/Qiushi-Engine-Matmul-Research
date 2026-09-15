import QiushiGlobalOrbitUnused305Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane305UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 30, (plane305UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane305UnusedGenConfig.planeBasis (i.val ^^^ (plane305UnusedGenConfig.sectionCode j).val) = true
abbrev plane305UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane305UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane305UnusedGenConfig.deadBasis (plane305UnusedGenConfig.deadCover i)) i.val = true
abbrev plane305UnusedGenSourceProperty (i : Fin 84) : Prop :=
  forall g : Nat, g ∈ plane305UnusedGenConfig.planeBasis -> spanContainsCode (plane305UnusedGenConfig.sourceBasis i) g = true
abbrev plane305UnusedGenDeadSourceProperty (i : Fin 1) : Prop :=
  forall g : Nat, g ∈ plane305UnusedGenConfig.planeBasis -> spanContainsCode (plane305UnusedGenConfig.deadBasis i) g = true
abbrev plane305UnusedGenIndicatorProperty (i : Fin 84) : Prop :=
  forall j : Fin 30, plane305UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane305UnusedGenConfig.sourceBasis i) (plane305UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
