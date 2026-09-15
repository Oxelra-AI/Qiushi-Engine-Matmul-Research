import QiushiGlobalOrbitUnused354Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane354UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 20, (plane354UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane354UnusedGenConfig.planeBasis (i.val ^^^ (plane354UnusedGenConfig.sectionCode j).val) = true
abbrev plane354UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane354UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane354UnusedGenConfig.deadBasis (plane354UnusedGenConfig.deadCover i)) i.val = true
abbrev plane354UnusedGenSourceProperty (i : Fin 30) : Prop :=
  forall g : Nat, g ∈ plane354UnusedGenConfig.planeBasis -> spanContainsCode (plane354UnusedGenConfig.sourceBasis i) g = true
abbrev plane354UnusedGenDeadSourceProperty (i : Fin 11) : Prop :=
  forall g : Nat, g ∈ plane354UnusedGenConfig.planeBasis -> spanContainsCode (plane354UnusedGenConfig.deadBasis i) g = true
abbrev plane354UnusedGenIndicatorProperty (i : Fin 30) : Prop :=
  forall j : Fin 20, plane354UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane354UnusedGenConfig.sourceBasis i) (plane354UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
