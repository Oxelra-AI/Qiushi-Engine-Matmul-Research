import QiushiGlobalOrbitUnused333Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane333UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 10, (plane333UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane333UnusedGenConfig.planeBasis (i.val ^^^ (plane333UnusedGenConfig.sectionCode j).val) = true
abbrev plane333UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane333UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane333UnusedGenConfig.deadBasis (plane333UnusedGenConfig.deadCover i)) i.val = true
abbrev plane333UnusedGenSourceProperty (i : Fin 36) : Prop :=
  forall g : Nat, g ∈ plane333UnusedGenConfig.planeBasis -> spanContainsCode (plane333UnusedGenConfig.sourceBasis i) g = true
abbrev plane333UnusedGenDeadSourceProperty (i : Fin 29) : Prop :=
  forall g : Nat, g ∈ plane333UnusedGenConfig.planeBasis -> spanContainsCode (plane333UnusedGenConfig.deadBasis i) g = true
abbrev plane333UnusedGenIndicatorProperty (i : Fin 36) : Prop :=
  forall j : Fin 10, plane333UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane333UnusedGenConfig.sourceBasis i) (plane333UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
