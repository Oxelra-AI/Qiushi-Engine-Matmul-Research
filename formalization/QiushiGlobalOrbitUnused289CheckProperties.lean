import QiushiGlobalOrbitUnused289Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane289UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 19, (plane289UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane289UnusedGenConfig.planeBasis (i.val ^^^ (plane289UnusedGenConfig.sectionCode j).val) = true
abbrev plane289UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane289UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane289UnusedGenConfig.deadBasis (plane289UnusedGenConfig.deadCover i)) i.val = true
abbrev plane289UnusedGenSourceProperty (i : Fin 27) : Prop :=
  forall g : Nat, g ∈ plane289UnusedGenConfig.planeBasis -> spanContainsCode (plane289UnusedGenConfig.sourceBasis i) g = true
abbrev plane289UnusedGenDeadSourceProperty (i : Fin 14) : Prop :=
  forall g : Nat, g ∈ plane289UnusedGenConfig.planeBasis -> spanContainsCode (plane289UnusedGenConfig.deadBasis i) g = true
abbrev plane289UnusedGenIndicatorProperty (i : Fin 27) : Prop :=
  forall j : Fin 19, plane289UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane289UnusedGenConfig.sourceBasis i) (plane289UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
