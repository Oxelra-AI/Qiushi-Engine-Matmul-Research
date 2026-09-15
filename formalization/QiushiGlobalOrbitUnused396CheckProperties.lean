import QiushiGlobalOrbitUnused396Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane396UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 14, (plane396UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane396UnusedGenConfig.planeBasis (i.val ^^^ (plane396UnusedGenConfig.sectionCode j).val) = true
abbrev plane396UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane396UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane396UnusedGenConfig.deadBasis (plane396UnusedGenConfig.deadCover i)) i.val = true
abbrev plane396UnusedGenSourceProperty (i : Fin 32) : Prop :=
  forall g : Nat, g ∈ plane396UnusedGenConfig.planeBasis -> spanContainsCode (plane396UnusedGenConfig.sourceBasis i) g = true
abbrev plane396UnusedGenDeadSourceProperty (i : Fin 19) : Prop :=
  forall g : Nat, g ∈ plane396UnusedGenConfig.planeBasis -> spanContainsCode (plane396UnusedGenConfig.deadBasis i) g = true
abbrev plane396UnusedGenIndicatorProperty (i : Fin 32) : Prop :=
  forall j : Fin 14, plane396UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane396UnusedGenConfig.sourceBasis i) (plane396UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
