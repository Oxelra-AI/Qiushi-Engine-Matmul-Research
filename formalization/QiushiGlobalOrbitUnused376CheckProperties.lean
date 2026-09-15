import QiushiGlobalOrbitUnused376Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane376UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 21, (plane376UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane376UnusedGenConfig.planeBasis (i.val ^^^ (plane376UnusedGenConfig.sectionCode j).val) = true
abbrev plane376UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane376UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane376UnusedGenConfig.deadBasis (plane376UnusedGenConfig.deadCover i)) i.val = true
abbrev plane376UnusedGenSourceProperty (i : Fin 15) : Prop :=
  forall g : Nat, g ∈ plane376UnusedGenConfig.planeBasis -> spanContainsCode (plane376UnusedGenConfig.sourceBasis i) g = true
abbrev plane376UnusedGenDeadSourceProperty (i : Fin 10) : Prop :=
  forall g : Nat, g ∈ plane376UnusedGenConfig.planeBasis -> spanContainsCode (plane376UnusedGenConfig.deadBasis i) g = true
abbrev plane376UnusedGenIndicatorProperty (i : Fin 15) : Prop :=
  forall j : Fin 21, plane376UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane376UnusedGenConfig.sourceBasis i) (plane376UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
