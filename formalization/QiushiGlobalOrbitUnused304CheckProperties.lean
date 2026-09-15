import QiushiGlobalOrbitUnused304Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane304UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 3, (plane304UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane304UnusedGenConfig.planeBasis (i.val ^^^ (plane304UnusedGenConfig.sectionCode j).val) = true
abbrev plane304UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane304UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane304UnusedGenConfig.deadBasis (plane304UnusedGenConfig.deadCover i)) i.val = true
abbrev plane304UnusedGenSourceProperty (i : Fin 35) : Prop :=
  forall g : Nat, g ∈ plane304UnusedGenConfig.planeBasis -> spanContainsCode (plane304UnusedGenConfig.sourceBasis i) g = true
abbrev plane304UnusedGenDeadSourceProperty (i : Fin 34) : Prop :=
  forall g : Nat, g ∈ plane304UnusedGenConfig.planeBasis -> spanContainsCode (plane304UnusedGenConfig.deadBasis i) g = true
abbrev plane304UnusedGenIndicatorProperty (i : Fin 35) : Prop :=
  forall j : Fin 3, plane304UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane304UnusedGenConfig.sourceBasis i) (plane304UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
