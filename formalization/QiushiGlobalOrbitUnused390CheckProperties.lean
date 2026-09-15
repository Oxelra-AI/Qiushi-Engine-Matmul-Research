import QiushiGlobalOrbitUnused390Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane390UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 14, (plane390UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane390UnusedGenConfig.planeBasis (i.val ^^^ (plane390UnusedGenConfig.sectionCode j).val) = true
abbrev plane390UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane390UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane390UnusedGenConfig.deadBasis (plane390UnusedGenConfig.deadCover i)) i.val = true
abbrev plane390UnusedGenSourceProperty (i : Fin 26) : Prop :=
  forall g : Nat, g ∈ plane390UnusedGenConfig.planeBasis -> spanContainsCode (plane390UnusedGenConfig.sourceBasis i) g = true
abbrev plane390UnusedGenDeadSourceProperty (i : Fin 18) : Prop :=
  forall g : Nat, g ∈ plane390UnusedGenConfig.planeBasis -> spanContainsCode (plane390UnusedGenConfig.deadBasis i) g = true
abbrev plane390UnusedGenIndicatorProperty (i : Fin 26) : Prop :=
  forall j : Fin 14, plane390UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane390UnusedGenConfig.sourceBasis i) (plane390UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
