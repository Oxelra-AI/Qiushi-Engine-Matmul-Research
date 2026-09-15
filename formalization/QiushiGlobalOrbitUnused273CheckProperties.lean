import QiushiGlobalOrbitUnused273Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane273UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 1, (plane273UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane273UnusedGenConfig.planeBasis (i.val ^^^ (plane273UnusedGenConfig.sectionCode j).val) = true
abbrev plane273UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane273UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane273UnusedGenConfig.deadBasis (plane273UnusedGenConfig.deadCover i)) i.val = true
abbrev plane273UnusedGenSourceProperty (i : Fin 44) : Prop :=
  forall g : Nat, g ∈ plane273UnusedGenConfig.planeBasis -> spanContainsCode (plane273UnusedGenConfig.sourceBasis i) g = true
abbrev plane273UnusedGenDeadSourceProperty (i : Fin 43) : Prop :=
  forall g : Nat, g ∈ plane273UnusedGenConfig.planeBasis -> spanContainsCode (plane273UnusedGenConfig.deadBasis i) g = true
abbrev plane273UnusedGenIndicatorProperty (i : Fin 44) : Prop :=
  forall j : Fin 1, plane273UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane273UnusedGenConfig.sourceBasis i) (plane273UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
