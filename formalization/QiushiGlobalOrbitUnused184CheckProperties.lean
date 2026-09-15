import QiushiGlobalOrbitUnused184Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane184UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 2, (plane184UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane184UnusedGenConfig.planeBasis (i.val ^^^ (plane184UnusedGenConfig.sectionCode j).val) = true
abbrev plane184UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane184UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane184UnusedGenConfig.deadBasis (plane184UnusedGenConfig.deadCover i)) i.val = true
abbrev plane184UnusedGenSourceProperty (i : Fin 14) : Prop :=
  forall g : Nat, g ∈ plane184UnusedGenConfig.planeBasis -> spanContainsCode (plane184UnusedGenConfig.sourceBasis i) g = true
abbrev plane184UnusedGenDeadSourceProperty (i : Fin 13) : Prop :=
  forall g : Nat, g ∈ plane184UnusedGenConfig.planeBasis -> spanContainsCode (plane184UnusedGenConfig.deadBasis i) g = true
abbrev plane184UnusedGenIndicatorProperty (i : Fin 14) : Prop :=
  forall j : Fin 2, plane184UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane184UnusedGenConfig.sourceBasis i) (plane184UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
