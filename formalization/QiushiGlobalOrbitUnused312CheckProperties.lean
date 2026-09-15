import QiushiGlobalOrbitUnused312Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane312UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 17, (plane312UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane312UnusedGenConfig.planeBasis (i.val ^^^ (plane312UnusedGenConfig.sectionCode j).val) = true
abbrev plane312UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane312UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane312UnusedGenConfig.deadBasis (plane312UnusedGenConfig.deadCover i)) i.val = true
abbrev plane312UnusedGenSourceProperty (i : Fin 20) : Prop :=
  forall g : Nat, g ∈ plane312UnusedGenConfig.planeBasis -> spanContainsCode (plane312UnusedGenConfig.sourceBasis i) g = true
abbrev plane312UnusedGenDeadSourceProperty (i : Fin 14) : Prop :=
  forall g : Nat, g ∈ plane312UnusedGenConfig.planeBasis -> spanContainsCode (plane312UnusedGenConfig.deadBasis i) g = true
abbrev plane312UnusedGenIndicatorProperty (i : Fin 20) : Prop :=
  forall j : Fin 17, plane312UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane312UnusedGenConfig.sourceBasis i) (plane312UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
