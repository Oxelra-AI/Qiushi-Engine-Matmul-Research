import QiushiGlobalOrbitUnused387Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane387UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 14, (plane387UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane387UnusedGenConfig.planeBasis (i.val ^^^ (plane387UnusedGenConfig.sectionCode j).val) = true
abbrev plane387UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane387UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane387UnusedGenConfig.deadBasis (plane387UnusedGenConfig.deadCover i)) i.val = true
abbrev plane387UnusedGenSourceProperty (i : Fin 32) : Prop :=
  forall g : Nat, g ∈ plane387UnusedGenConfig.planeBasis -> spanContainsCode (plane387UnusedGenConfig.sourceBasis i) g = true
abbrev plane387UnusedGenDeadSourceProperty (i : Fin 20) : Prop :=
  forall g : Nat, g ∈ plane387UnusedGenConfig.planeBasis -> spanContainsCode (plane387UnusedGenConfig.deadBasis i) g = true
abbrev plane387UnusedGenIndicatorProperty (i : Fin 32) : Prop :=
  forall j : Fin 14, plane387UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane387UnusedGenConfig.sourceBasis i) (plane387UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
