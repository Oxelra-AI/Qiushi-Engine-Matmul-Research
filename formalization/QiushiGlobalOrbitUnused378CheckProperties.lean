import QiushiGlobalOrbitUnused378Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane378UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 15, (plane378UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane378UnusedGenConfig.planeBasis (i.val ^^^ (plane378UnusedGenConfig.sectionCode j).val) = true
abbrev plane378UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane378UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane378UnusedGenConfig.deadBasis (plane378UnusedGenConfig.deadCover i)) i.val = true
abbrev plane378UnusedGenSourceProperty (i : Fin 17) : Prop :=
  forall g : Nat, g ∈ plane378UnusedGenConfig.planeBasis -> spanContainsCode (plane378UnusedGenConfig.sourceBasis i) g = true
abbrev plane378UnusedGenDeadSourceProperty (i : Fin 16) : Prop :=
  forall g : Nat, g ∈ plane378UnusedGenConfig.planeBasis -> spanContainsCode (plane378UnusedGenConfig.deadBasis i) g = true
abbrev plane378UnusedGenIndicatorProperty (i : Fin 17) : Prop :=
  forall j : Fin 15, plane378UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane378UnusedGenConfig.sourceBasis i) (plane378UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
