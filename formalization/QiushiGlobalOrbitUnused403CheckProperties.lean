import QiushiGlobalOrbitUnused403Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane403UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 18, (plane403UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane403UnusedGenConfig.planeBasis (i.val ^^^ (plane403UnusedGenConfig.sectionCode j).val) = true
abbrev plane403UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane403UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane403UnusedGenConfig.deadBasis (plane403UnusedGenConfig.deadCover i)) i.val = true
abbrev plane403UnusedGenSourceProperty (i : Fin 16) : Prop :=
  forall g : Nat, g ∈ plane403UnusedGenConfig.planeBasis -> spanContainsCode (plane403UnusedGenConfig.sourceBasis i) g = true
abbrev plane403UnusedGenDeadSourceProperty (i : Fin 13) : Prop :=
  forall g : Nat, g ∈ plane403UnusedGenConfig.planeBasis -> spanContainsCode (plane403UnusedGenConfig.deadBasis i) g = true
abbrev plane403UnusedGenIndicatorProperty (i : Fin 16) : Prop :=
  forall j : Fin 18, plane403UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane403UnusedGenConfig.sourceBasis i) (plane403UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
