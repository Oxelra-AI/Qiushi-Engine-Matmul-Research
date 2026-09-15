import QiushiGlobalOrbitUnused181Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane181UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 3, (plane181UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane181UnusedGenConfig.planeBasis (i.val ^^^ (plane181UnusedGenConfig.sectionCode j).val) = true
abbrev plane181UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane181UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane181UnusedGenConfig.deadBasis (plane181UnusedGenConfig.deadCover i)) i.val = true
abbrev plane181UnusedGenSourceProperty (i : Fin 13) : Prop :=
  forall g : Nat, g ∈ plane181UnusedGenConfig.planeBasis -> spanContainsCode (plane181UnusedGenConfig.sourceBasis i) g = true
abbrev plane181UnusedGenDeadSourceProperty (i : Fin 12) : Prop :=
  forall g : Nat, g ∈ plane181UnusedGenConfig.planeBasis -> spanContainsCode (plane181UnusedGenConfig.deadBasis i) g = true
abbrev plane181UnusedGenIndicatorProperty (i : Fin 13) : Prop :=
  forall j : Fin 3, plane181UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane181UnusedGenConfig.sourceBasis i) (plane181UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
