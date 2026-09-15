import QiushiGlobalOrbitUnused284Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane284UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 2, (plane284UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane284UnusedGenConfig.planeBasis (i.val ^^^ (plane284UnusedGenConfig.sectionCode j).val) = true
abbrev plane284UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane284UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane284UnusedGenConfig.deadBasis (plane284UnusedGenConfig.deadCover i)) i.val = true
abbrev plane284UnusedGenSourceProperty (i : Fin 34) : Prop :=
  forall g : Nat, g ∈ plane284UnusedGenConfig.planeBasis -> spanContainsCode (plane284UnusedGenConfig.sourceBasis i) g = true
abbrev plane284UnusedGenDeadSourceProperty (i : Fin 33) : Prop :=
  forall g : Nat, g ∈ plane284UnusedGenConfig.planeBasis -> spanContainsCode (plane284UnusedGenConfig.deadBasis i) g = true
abbrev plane284UnusedGenIndicatorProperty (i : Fin 34) : Prop :=
  forall j : Fin 2, plane284UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane284UnusedGenConfig.sourceBasis i) (plane284UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
