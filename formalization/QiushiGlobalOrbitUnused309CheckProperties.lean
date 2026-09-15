import QiushiGlobalOrbitUnused309Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane309UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 15, (plane309UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane309UnusedGenConfig.planeBasis (i.val ^^^ (plane309UnusedGenConfig.sectionCode j).val) = true
abbrev plane309UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane309UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane309UnusedGenConfig.deadBasis (plane309UnusedGenConfig.deadCover i)) i.val = true
abbrev plane309UnusedGenSourceProperty (i : Fin 28) : Prop :=
  forall g : Nat, g ∈ plane309UnusedGenConfig.planeBasis -> spanContainsCode (plane309UnusedGenConfig.sourceBasis i) g = true
abbrev plane309UnusedGenDeadSourceProperty (i : Fin 16) : Prop :=
  forall g : Nat, g ∈ plane309UnusedGenConfig.planeBasis -> spanContainsCode (plane309UnusedGenConfig.deadBasis i) g = true
abbrev plane309UnusedGenIndicatorProperty (i : Fin 28) : Prop :=
  forall j : Fin 15, plane309UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane309UnusedGenConfig.sourceBasis i) (plane309UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
