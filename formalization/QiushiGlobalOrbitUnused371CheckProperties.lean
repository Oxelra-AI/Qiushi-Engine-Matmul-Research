import QiushiGlobalOrbitUnused371Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane371UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 18, (plane371UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane371UnusedGenConfig.planeBasis (i.val ^^^ (plane371UnusedGenConfig.sectionCode j).val) = true
abbrev plane371UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane371UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane371UnusedGenConfig.deadBasis (plane371UnusedGenConfig.deadCover i)) i.val = true
abbrev plane371UnusedGenSourceProperty (i : Fin 38) : Prop :=
  forall g : Nat, g ∈ plane371UnusedGenConfig.planeBasis -> spanContainsCode (plane371UnusedGenConfig.sourceBasis i) g = true
abbrev plane371UnusedGenDeadSourceProperty (i : Fin 14) : Prop :=
  forall g : Nat, g ∈ plane371UnusedGenConfig.planeBasis -> spanContainsCode (plane371UnusedGenConfig.deadBasis i) g = true
abbrev plane371UnusedGenIndicatorProperty (i : Fin 38) : Prop :=
  forall j : Fin 18, plane371UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane371UnusedGenConfig.sourceBasis i) (plane371UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
