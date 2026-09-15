import QiushiGlobalOrbitUnused353Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane353UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 20, (plane353UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane353UnusedGenConfig.planeBasis (i.val ^^^ (plane353UnusedGenConfig.sectionCode j).val) = true
abbrev plane353UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane353UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane353UnusedGenConfig.deadBasis (plane353UnusedGenConfig.deadCover i)) i.val = true
abbrev plane353UnusedGenSourceProperty (i : Fin 39) : Prop :=
  forall g : Nat, g ∈ plane353UnusedGenConfig.planeBasis -> spanContainsCode (plane353UnusedGenConfig.sourceBasis i) g = true
abbrev plane353UnusedGenDeadSourceProperty (i : Fin 11) : Prop :=
  forall g : Nat, g ∈ plane353UnusedGenConfig.planeBasis -> spanContainsCode (plane353UnusedGenConfig.deadBasis i) g = true
abbrev plane353UnusedGenIndicatorProperty (i : Fin 39) : Prop :=
  forall j : Fin 20, plane353UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane353UnusedGenConfig.sourceBasis i) (plane353UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
