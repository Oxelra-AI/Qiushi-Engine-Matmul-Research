import QiushiGlobalOrbitUnused92Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane92UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 9, (plane92UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane92UnusedGenConfig.planeBasis (i.val ^^^ (plane92UnusedGenConfig.sectionCode j).val) = true
abbrev plane92UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane92UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane92UnusedGenConfig.deadBasis (plane92UnusedGenConfig.deadCover i)) i.val = true
abbrev plane92UnusedGenSourceProperty (i : Fin 11) : Prop :=
  forall g : Nat, g ∈ plane92UnusedGenConfig.planeBasis -> spanContainsCode (plane92UnusedGenConfig.sourceBasis i) g = true
abbrev plane92UnusedGenDeadSourceProperty (i : Fin 6) : Prop :=
  forall g : Nat, g ∈ plane92UnusedGenConfig.planeBasis -> spanContainsCode (plane92UnusedGenConfig.deadBasis i) g = true
abbrev plane92UnusedGenIndicatorProperty (i : Fin 11) : Prop :=
  forall j : Fin 9, plane92UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane92UnusedGenConfig.sourceBasis i) (plane92UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
