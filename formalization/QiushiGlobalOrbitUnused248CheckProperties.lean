import QiushiGlobalOrbitUnused248Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane248UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 28, (plane248UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane248UnusedGenConfig.planeBasis (i.val ^^^ (plane248UnusedGenConfig.sectionCode j).val) = true
abbrev plane248UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane248UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane248UnusedGenConfig.deadBasis (plane248UnusedGenConfig.deadCover i)) i.val = true
abbrev plane248UnusedGenSourceProperty (i : Fin 23) : Prop :=
  forall g : Nat, g ∈ plane248UnusedGenConfig.planeBasis -> spanContainsCode (plane248UnusedGenConfig.sourceBasis i) g = true
abbrev plane248UnusedGenDeadSourceProperty (i : Fin 3) : Prop :=
  forall g : Nat, g ∈ plane248UnusedGenConfig.planeBasis -> spanContainsCode (plane248UnusedGenConfig.deadBasis i) g = true
abbrev plane248UnusedGenIndicatorProperty (i : Fin 23) : Prop :=
  forall j : Fin 28, plane248UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane248UnusedGenConfig.sourceBasis i) (plane248UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
