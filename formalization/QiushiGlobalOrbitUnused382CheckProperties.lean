import QiushiGlobalOrbitUnused382Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane382UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 12, (plane382UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane382UnusedGenConfig.planeBasis (i.val ^^^ (plane382UnusedGenConfig.sectionCode j).val) = true
abbrev plane382UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane382UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane382UnusedGenConfig.deadBasis (plane382UnusedGenConfig.deadCover i)) i.val = true
abbrev plane382UnusedGenSourceProperty (i : Fin 23) : Prop :=
  forall g : Nat, g ∈ plane382UnusedGenConfig.planeBasis -> spanContainsCode (plane382UnusedGenConfig.sourceBasis i) g = true
abbrev plane382UnusedGenDeadSourceProperty (i : Fin 19) : Prop :=
  forall g : Nat, g ∈ plane382UnusedGenConfig.planeBasis -> spanContainsCode (plane382UnusedGenConfig.deadBasis i) g = true
abbrev plane382UnusedGenIndicatorProperty (i : Fin 23) : Prop :=
  forall j : Fin 12, plane382UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane382UnusedGenConfig.sourceBasis i) (plane382UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
