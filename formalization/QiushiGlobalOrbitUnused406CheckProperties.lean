import QiushiGlobalOrbitUnused406Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane406UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 17, (plane406UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane406UnusedGenConfig.planeBasis (i.val ^^^ (plane406UnusedGenConfig.sectionCode j).val) = true
abbrev plane406UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane406UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane406UnusedGenConfig.deadBasis (plane406UnusedGenConfig.deadCover i)) i.val = true
abbrev plane406UnusedGenSourceProperty (i : Fin 18) : Prop :=
  forall g : Nat, g ∈ plane406UnusedGenConfig.planeBasis -> spanContainsCode (plane406UnusedGenConfig.sourceBasis i) g = true
abbrev plane406UnusedGenDeadSourceProperty (i : Fin 14) : Prop :=
  forall g : Nat, g ∈ plane406UnusedGenConfig.planeBasis -> spanContainsCode (plane406UnusedGenConfig.deadBasis i) g = true
abbrev plane406UnusedGenIndicatorProperty (i : Fin 18) : Prop :=
  forall j : Fin 17, plane406UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane406UnusedGenConfig.sourceBasis i) (plane406UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
