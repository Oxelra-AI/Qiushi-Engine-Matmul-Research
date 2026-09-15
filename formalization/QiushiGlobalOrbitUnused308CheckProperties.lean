import QiushiGlobalOrbitUnused308Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane308UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 14, (plane308UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane308UnusedGenConfig.planeBasis (i.val ^^^ (plane308UnusedGenConfig.sectionCode j).val) = true
abbrev plane308UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane308UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane308UnusedGenConfig.deadBasis (plane308UnusedGenConfig.deadCover i)) i.val = true
abbrev plane308UnusedGenSourceProperty (i : Fin 28) : Prop :=
  forall g : Nat, g ∈ plane308UnusedGenConfig.planeBasis -> spanContainsCode (plane308UnusedGenConfig.sourceBasis i) g = true
abbrev plane308UnusedGenDeadSourceProperty (i : Fin 19) : Prop :=
  forall g : Nat, g ∈ plane308UnusedGenConfig.planeBasis -> spanContainsCode (plane308UnusedGenConfig.deadBasis i) g = true
abbrev plane308UnusedGenIndicatorProperty (i : Fin 28) : Prop :=
  forall j : Fin 14, plane308UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane308UnusedGenConfig.sourceBasis i) (plane308UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
