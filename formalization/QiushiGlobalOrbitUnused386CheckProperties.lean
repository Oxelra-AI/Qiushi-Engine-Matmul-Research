import QiushiGlobalOrbitUnused386Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane386UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 19, (plane386UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane386UnusedGenConfig.planeBasis (i.val ^^^ (plane386UnusedGenConfig.sectionCode j).val) = true
abbrev plane386UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane386UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane386UnusedGenConfig.deadBasis (plane386UnusedGenConfig.deadCover i)) i.val = true
abbrev plane386UnusedGenSourceProperty (i : Fin 21) : Prop :=
  forall g : Nat, g ∈ plane386UnusedGenConfig.planeBasis -> spanContainsCode (plane386UnusedGenConfig.sourceBasis i) g = true
abbrev plane386UnusedGenDeadSourceProperty (i : Fin 13) : Prop :=
  forall g : Nat, g ∈ plane386UnusedGenConfig.planeBasis -> spanContainsCode (plane386UnusedGenConfig.deadBasis i) g = true
abbrev plane386UnusedGenIndicatorProperty (i : Fin 21) : Prop :=
  forall j : Fin 19, plane386UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane386UnusedGenConfig.sourceBasis i) (plane386UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
