import QiushiGlobalOrbitUnused392Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane392UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 9, (plane392UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane392UnusedGenConfig.planeBasis (i.val ^^^ (plane392UnusedGenConfig.sectionCode j).val) = true
abbrev plane392UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane392UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane392UnusedGenConfig.deadBasis (plane392UnusedGenConfig.deadCover i)) i.val = true
abbrev plane392UnusedGenSourceProperty (i : Fin 25) : Prop :=
  forall g : Nat, g ∈ plane392UnusedGenConfig.planeBasis -> spanContainsCode (plane392UnusedGenConfig.sourceBasis i) g = true
abbrev plane392UnusedGenDeadSourceProperty (i : Fin 24) : Prop :=
  forall g : Nat, g ∈ plane392UnusedGenConfig.planeBasis -> spanContainsCode (plane392UnusedGenConfig.deadBasis i) g = true
abbrev plane392UnusedGenIndicatorProperty (i : Fin 25) : Prop :=
  forall j : Fin 9, plane392UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane392UnusedGenConfig.sourceBasis i) (plane392UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
