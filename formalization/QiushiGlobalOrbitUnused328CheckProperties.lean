import QiushiGlobalOrbitUnused328Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane328UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 8, (plane328UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane328UnusedGenConfig.planeBasis (i.val ^^^ (plane328UnusedGenConfig.sectionCode j).val) = true
abbrev plane328UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane328UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane328UnusedGenConfig.deadBasis (plane328UnusedGenConfig.deadCover i)) i.val = true
abbrev plane328UnusedGenSourceProperty (i : Fin 29) : Prop :=
  forall g : Nat, g ∈ plane328UnusedGenConfig.planeBasis -> spanContainsCode (plane328UnusedGenConfig.sourceBasis i) g = true
abbrev plane328UnusedGenDeadSourceProperty (i : Fin 25) : Prop :=
  forall g : Nat, g ∈ plane328UnusedGenConfig.planeBasis -> spanContainsCode (plane328UnusedGenConfig.deadBasis i) g = true
abbrev plane328UnusedGenIndicatorProperty (i : Fin 29) : Prop :=
  forall j : Fin 8, plane328UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane328UnusedGenConfig.sourceBasis i) (plane328UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
