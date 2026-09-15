import QiushiGlobalOrbitUnused383Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane383UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 12, (plane383UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane383UnusedGenConfig.planeBasis (i.val ^^^ (plane383UnusedGenConfig.sectionCode j).val) = true
abbrev plane383UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane383UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane383UnusedGenConfig.deadBasis (plane383UnusedGenConfig.deadCover i)) i.val = true
abbrev plane383UnusedGenSourceProperty (i : Fin 28) : Prop :=
  forall g : Nat, g ∈ plane383UnusedGenConfig.planeBasis -> spanContainsCode (plane383UnusedGenConfig.sourceBasis i) g = true
abbrev plane383UnusedGenDeadSourceProperty (i : Fin 19) : Prop :=
  forall g : Nat, g ∈ plane383UnusedGenConfig.planeBasis -> spanContainsCode (plane383UnusedGenConfig.deadBasis i) g = true
abbrev plane383UnusedGenIndicatorProperty (i : Fin 28) : Prop :=
  forall j : Fin 12, plane383UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane383UnusedGenConfig.sourceBasis i) (plane383UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
