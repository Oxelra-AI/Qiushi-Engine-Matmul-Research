import QiushiGlobalOrbitUnused380Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane380UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 10, (plane380UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane380UnusedGenConfig.planeBasis (i.val ^^^ (plane380UnusedGenConfig.sectionCode j).val) = true
abbrev plane380UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane380UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane380UnusedGenConfig.deadBasis (plane380UnusedGenConfig.deadCover i)) i.val = true
abbrev plane380UnusedGenSourceProperty (i : Fin 26) : Prop :=
  forall g : Nat, g ∈ plane380UnusedGenConfig.planeBasis -> spanContainsCode (plane380UnusedGenConfig.sourceBasis i) g = true
abbrev plane380UnusedGenDeadSourceProperty (i : Fin 21) : Prop :=
  forall g : Nat, g ∈ plane380UnusedGenConfig.planeBasis -> spanContainsCode (plane380UnusedGenConfig.deadBasis i) g = true
abbrev plane380UnusedGenIndicatorProperty (i : Fin 26) : Prop :=
  forall j : Fin 10, plane380UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane380UnusedGenConfig.sourceBasis i) (plane380UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
