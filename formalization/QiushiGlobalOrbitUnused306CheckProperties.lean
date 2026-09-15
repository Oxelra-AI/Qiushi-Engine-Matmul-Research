import QiushiGlobalOrbitUnused306Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane306UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 17, (plane306UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane306UnusedGenConfig.planeBasis (i.val ^^^ (plane306UnusedGenConfig.sectionCode j).val) = true
abbrev plane306UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane306UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane306UnusedGenConfig.deadBasis (plane306UnusedGenConfig.deadCover i)) i.val = true
abbrev plane306UnusedGenSourceProperty (i : Fin 30) : Prop :=
  forall g : Nat, g ∈ plane306UnusedGenConfig.planeBasis -> spanContainsCode (plane306UnusedGenConfig.sourceBasis i) g = true
abbrev plane306UnusedGenDeadSourceProperty (i : Fin 14) : Prop :=
  forall g : Nat, g ∈ plane306UnusedGenConfig.planeBasis -> spanContainsCode (plane306UnusedGenConfig.deadBasis i) g = true
abbrev plane306UnusedGenIndicatorProperty (i : Fin 30) : Prop :=
  forall j : Fin 17, plane306UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane306UnusedGenConfig.sourceBasis i) (plane306UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
