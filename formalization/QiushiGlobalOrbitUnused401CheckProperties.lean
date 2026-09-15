import QiushiGlobalOrbitUnused401Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane401UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 9, (plane401UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane401UnusedGenConfig.planeBasis (i.val ^^^ (plane401UnusedGenConfig.sectionCode j).val) = true
abbrev plane401UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane401UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane401UnusedGenConfig.deadBasis (plane401UnusedGenConfig.deadCover i)) i.val = true
abbrev plane401UnusedGenSourceProperty (i : Fin 30) : Prop :=
  forall g : Nat, g ∈ plane401UnusedGenConfig.planeBasis -> spanContainsCode (plane401UnusedGenConfig.sourceBasis i) g = true
abbrev plane401UnusedGenDeadSourceProperty (i : Fin 23) : Prop :=
  forall g : Nat, g ∈ plane401UnusedGenConfig.planeBasis -> spanContainsCode (plane401UnusedGenConfig.deadBasis i) g = true
abbrev plane401UnusedGenIndicatorProperty (i : Fin 30) : Prop :=
  forall j : Fin 9, plane401UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane401UnusedGenConfig.sourceBasis i) (plane401UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
