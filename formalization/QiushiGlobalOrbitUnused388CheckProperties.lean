import QiushiGlobalOrbitUnused388Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane388UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 13, (plane388UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane388UnusedGenConfig.planeBasis (i.val ^^^ (plane388UnusedGenConfig.sectionCode j).val) = true
abbrev plane388UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane388UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane388UnusedGenConfig.deadBasis (plane388UnusedGenConfig.deadCover i)) i.val = true
abbrev plane388UnusedGenSourceProperty (i : Fin 28) : Prop :=
  forall g : Nat, g ∈ plane388UnusedGenConfig.planeBasis -> spanContainsCode (plane388UnusedGenConfig.sourceBasis i) g = true
abbrev plane388UnusedGenDeadSourceProperty (i : Fin 21) : Prop :=
  forall g : Nat, g ∈ plane388UnusedGenConfig.planeBasis -> spanContainsCode (plane388UnusedGenConfig.deadBasis i) g = true
abbrev plane388UnusedGenIndicatorProperty (i : Fin 28) : Prop :=
  forall j : Fin 13, plane388UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane388UnusedGenConfig.sourceBasis i) (plane388UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
