import QiushiGlobalOrbitUnused379Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane379UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 16, (plane379UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane379UnusedGenConfig.planeBasis (i.val ^^^ (plane379UnusedGenConfig.sectionCode j).val) = true
abbrev plane379UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane379UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane379UnusedGenConfig.deadBasis (plane379UnusedGenConfig.deadCover i)) i.val = true
abbrev plane379UnusedGenSourceProperty (i : Fin 22) : Prop :=
  forall g : Nat, g ∈ plane379UnusedGenConfig.planeBasis -> spanContainsCode (plane379UnusedGenConfig.sourceBasis i) g = true
abbrev plane379UnusedGenDeadSourceProperty (i : Fin 15) : Prop :=
  forall g : Nat, g ∈ plane379UnusedGenConfig.planeBasis -> spanContainsCode (plane379UnusedGenConfig.deadBasis i) g = true
abbrev plane379UnusedGenIndicatorProperty (i : Fin 22) : Prop :=
  forall j : Fin 16, plane379UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane379UnusedGenConfig.sourceBasis i) (plane379UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
