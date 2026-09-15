import QiushiGlobalOrbitUnused372Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane372UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 26, (plane372UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane372UnusedGenConfig.planeBasis (i.val ^^^ (plane372UnusedGenConfig.sectionCode j).val) = true
abbrev plane372UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane372UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane372UnusedGenConfig.deadBasis (plane372UnusedGenConfig.deadCover i)) i.val = true
abbrev plane372UnusedGenSourceProperty (i : Fin 37) : Prop :=
  forall g : Nat, g ∈ plane372UnusedGenConfig.planeBasis -> spanContainsCode (plane372UnusedGenConfig.sourceBasis i) g = true
abbrev plane372UnusedGenDeadSourceProperty (i : Fin 5) : Prop :=
  forall g : Nat, g ∈ plane372UnusedGenConfig.planeBasis -> spanContainsCode (plane372UnusedGenConfig.deadBasis i) g = true
abbrev plane372UnusedGenIndicatorProperty (i : Fin 37) : Prop :=
  forall j : Fin 26, plane372UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane372UnusedGenConfig.sourceBasis i) (plane372UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
