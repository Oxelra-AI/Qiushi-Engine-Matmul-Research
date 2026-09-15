import QiushiGlobalOrbitUnused249Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane249UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 28, (plane249UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane249UnusedGenConfig.planeBasis (i.val ^^^ (plane249UnusedGenConfig.sectionCode j).val) = true
abbrev plane249UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane249UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane249UnusedGenConfig.deadBasis (plane249UnusedGenConfig.deadCover i)) i.val = true
abbrev plane249UnusedGenSourceProperty (i : Fin 29) : Prop :=
  forall g : Nat, g ∈ plane249UnusedGenConfig.planeBasis -> spanContainsCode (plane249UnusedGenConfig.sourceBasis i) g = true
abbrev plane249UnusedGenDeadSourceProperty (i : Fin 3) : Prop :=
  forall g : Nat, g ∈ plane249UnusedGenConfig.planeBasis -> spanContainsCode (plane249UnusedGenConfig.deadBasis i) g = true
abbrev plane249UnusedGenIndicatorProperty (i : Fin 29) : Prop :=
  forall j : Fin 28, plane249UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane249UnusedGenConfig.sourceBasis i) (plane249UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
