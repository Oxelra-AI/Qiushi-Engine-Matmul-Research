import QiushiGlobalOrbitUnused402Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane402UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 13, (plane402UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane402UnusedGenConfig.planeBasis (i.val ^^^ (plane402UnusedGenConfig.sectionCode j).val) = true
abbrev plane402UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane402UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane402UnusedGenConfig.deadBasis (plane402UnusedGenConfig.deadCover i)) i.val = true
abbrev plane402UnusedGenSourceProperty (i : Fin 31) : Prop :=
  forall g : Nat, g ∈ plane402UnusedGenConfig.planeBasis -> spanContainsCode (plane402UnusedGenConfig.sourceBasis i) g = true
abbrev plane402UnusedGenDeadSourceProperty (i : Fin 19) : Prop :=
  forall g : Nat, g ∈ plane402UnusedGenConfig.planeBasis -> spanContainsCode (plane402UnusedGenConfig.deadBasis i) g = true
abbrev plane402UnusedGenIndicatorProperty (i : Fin 31) : Prop :=
  forall j : Fin 13, plane402UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane402UnusedGenConfig.sourceBasis i) (plane402UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
