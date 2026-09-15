import QiushiGlobalOrbitUnused389Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane389UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 14, (plane389UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane389UnusedGenConfig.planeBasis (i.val ^^^ (plane389UnusedGenConfig.sectionCode j).val) = true
abbrev plane389UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane389UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane389UnusedGenConfig.deadBasis (plane389UnusedGenConfig.deadCover i)) i.val = true
abbrev plane389UnusedGenSourceProperty (i : Fin 35) : Prop :=
  forall g : Nat, g ∈ plane389UnusedGenConfig.planeBasis -> spanContainsCode (plane389UnusedGenConfig.sourceBasis i) g = true
abbrev plane389UnusedGenDeadSourceProperty (i : Fin 24) : Prop :=
  forall g : Nat, g ∈ plane389UnusedGenConfig.planeBasis -> spanContainsCode (plane389UnusedGenConfig.deadBasis i) g = true
abbrev plane389UnusedGenIndicatorProperty (i : Fin 35) : Prop :=
  forall j : Fin 14, plane389UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane389UnusedGenConfig.sourceBasis i) (plane389UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
