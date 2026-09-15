import QiushiGlobalOrbitUnused404Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane404UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 14, (plane404UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane404UnusedGenConfig.planeBasis (i.val ^^^ (plane404UnusedGenConfig.sectionCode j).val) = true
abbrev plane404UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane404UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane404UnusedGenConfig.deadBasis (plane404UnusedGenConfig.deadCover i)) i.val = true
abbrev plane404UnusedGenSourceProperty (i : Fin 31) : Prop :=
  forall g : Nat, g ∈ plane404UnusedGenConfig.planeBasis -> spanContainsCode (plane404UnusedGenConfig.sourceBasis i) g = true
abbrev plane404UnusedGenDeadSourceProperty (i : Fin 17) : Prop :=
  forall g : Nat, g ∈ plane404UnusedGenConfig.planeBasis -> spanContainsCode (plane404UnusedGenConfig.deadBasis i) g = true
abbrev plane404UnusedGenIndicatorProperty (i : Fin 31) : Prop :=
  forall j : Fin 14, plane404UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane404UnusedGenConfig.sourceBasis i) (plane404UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
