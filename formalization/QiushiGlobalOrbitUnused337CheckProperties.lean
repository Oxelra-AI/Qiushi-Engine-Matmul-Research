import QiushiGlobalOrbitUnused337Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane337UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 8, (plane337UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane337UnusedGenConfig.planeBasis (i.val ^^^ (plane337UnusedGenConfig.sectionCode j).val) = true
abbrev plane337UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane337UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane337UnusedGenConfig.deadBasis (plane337UnusedGenConfig.deadCover i)) i.val = true
abbrev plane337UnusedGenSourceProperty (i : Fin 30) : Prop :=
  forall g : Nat, g ∈ plane337UnusedGenConfig.planeBasis -> spanContainsCode (plane337UnusedGenConfig.sourceBasis i) g = true
abbrev plane337UnusedGenDeadSourceProperty (i : Fin 27) : Prop :=
  forall g : Nat, g ∈ plane337UnusedGenConfig.planeBasis -> spanContainsCode (plane337UnusedGenConfig.deadBasis i) g = true
abbrev plane337UnusedGenIndicatorProperty (i : Fin 30) : Prop :=
  forall j : Fin 8, plane337UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane337UnusedGenConfig.sourceBasis i) (plane337UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
