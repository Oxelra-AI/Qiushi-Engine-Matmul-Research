import QiushiGlobalOrbitUnused399Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane399UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 17, (plane399UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane399UnusedGenConfig.planeBasis (i.val ^^^ (plane399UnusedGenConfig.sectionCode j).val) = true
abbrev plane399UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane399UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane399UnusedGenConfig.deadBasis (plane399UnusedGenConfig.deadCover i)) i.val = true
abbrev plane399UnusedGenSourceProperty (i : Fin 25) : Prop :=
  forall g : Nat, g ∈ plane399UnusedGenConfig.planeBasis -> spanContainsCode (plane399UnusedGenConfig.sourceBasis i) g = true
abbrev plane399UnusedGenDeadSourceProperty (i : Fin 18) : Prop :=
  forall g : Nat, g ∈ plane399UnusedGenConfig.planeBasis -> spanContainsCode (plane399UnusedGenConfig.deadBasis i) g = true
abbrev plane399UnusedGenIndicatorProperty (i : Fin 25) : Prop :=
  forall j : Fin 17, plane399UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane399UnusedGenConfig.sourceBasis i) (plane399UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
