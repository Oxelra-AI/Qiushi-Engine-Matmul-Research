import QiushiGlobalOrbitUnused302Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane302UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 9, (plane302UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane302UnusedGenConfig.planeBasis (i.val ^^^ (plane302UnusedGenConfig.sectionCode j).val) = true
abbrev plane302UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane302UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane302UnusedGenConfig.deadBasis (plane302UnusedGenConfig.deadCover i)) i.val = true
abbrev plane302UnusedGenSourceProperty (i : Fin 25) : Prop :=
  forall g : Nat, g ∈ plane302UnusedGenConfig.planeBasis -> spanContainsCode (plane302UnusedGenConfig.sourceBasis i) g = true
abbrev plane302UnusedGenDeadSourceProperty (i : Fin 22) : Prop :=
  forall g : Nat, g ∈ plane302UnusedGenConfig.planeBasis -> spanContainsCode (plane302UnusedGenConfig.deadBasis i) g = true
abbrev plane302UnusedGenIndicatorProperty (i : Fin 25) : Prop :=
  forall j : Fin 9, plane302UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane302UnusedGenConfig.sourceBasis i) (plane302UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
