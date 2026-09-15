import QiushiGlobalOrbitUnused291Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane291UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 3, (plane291UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane291UnusedGenConfig.planeBasis (i.val ^^^ (plane291UnusedGenConfig.sectionCode j).val) = true
abbrev plane291UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane291UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane291UnusedGenConfig.deadBasis (plane291UnusedGenConfig.deadCover i)) i.val = true
abbrev plane291UnusedGenSourceProperty (i : Fin 33) : Prop :=
  forall g : Nat, g ∈ plane291UnusedGenConfig.planeBasis -> spanContainsCode (plane291UnusedGenConfig.sourceBasis i) g = true
abbrev plane291UnusedGenDeadSourceProperty (i : Fin 30) : Prop :=
  forall g : Nat, g ∈ plane291UnusedGenConfig.planeBasis -> spanContainsCode (plane291UnusedGenConfig.deadBasis i) g = true
abbrev plane291UnusedGenIndicatorProperty (i : Fin 33) : Prop :=
  forall j : Fin 3, plane291UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane291UnusedGenConfig.sourceBasis i) (plane291UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
