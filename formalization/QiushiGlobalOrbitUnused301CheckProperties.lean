import QiushiGlobalOrbitUnused301Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane301UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 13, (plane301UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane301UnusedGenConfig.planeBasis (i.val ^^^ (plane301UnusedGenConfig.sectionCode j).val) = true
abbrev plane301UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane301UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane301UnusedGenConfig.deadBasis (plane301UnusedGenConfig.deadCover i)) i.val = true
abbrev plane301UnusedGenSourceProperty (i : Fin 20) : Prop :=
  forall g : Nat, g ∈ plane301UnusedGenConfig.planeBasis -> spanContainsCode (plane301UnusedGenConfig.sourceBasis i) g = true
abbrev plane301UnusedGenDeadSourceProperty (i : Fin 18) : Prop :=
  forall g : Nat, g ∈ plane301UnusedGenConfig.planeBasis -> spanContainsCode (plane301UnusedGenConfig.deadBasis i) g = true
abbrev plane301UnusedGenIndicatorProperty (i : Fin 20) : Prop :=
  forall j : Fin 13, plane301UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane301UnusedGenConfig.sourceBasis i) (plane301UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
