import QiushiGlobalOrbitUnused203Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane203UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 4, (plane203UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane203UnusedGenConfig.planeBasis (i.val ^^^ (plane203UnusedGenConfig.sectionCode j).val) = true
abbrev plane203UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane203UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane203UnusedGenConfig.deadBasis (plane203UnusedGenConfig.deadCover i)) i.val = true
abbrev plane203UnusedGenSourceProperty (i : Fin 15) : Prop :=
  forall g : Nat, g ∈ plane203UnusedGenConfig.planeBasis -> spanContainsCode (plane203UnusedGenConfig.sourceBasis i) g = true
abbrev plane203UnusedGenDeadSourceProperty (i : Fin 11) : Prop :=
  forall g : Nat, g ∈ plane203UnusedGenConfig.planeBasis -> spanContainsCode (plane203UnusedGenConfig.deadBasis i) g = true
abbrev plane203UnusedGenIndicatorProperty (i : Fin 15) : Prop :=
  forall j : Fin 4, plane203UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane203UnusedGenConfig.sourceBasis i) (plane203UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
