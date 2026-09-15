import QiushiGlobalOrbitUnused355Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane355UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 22, (plane355UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane355UnusedGenConfig.planeBasis (i.val ^^^ (plane355UnusedGenConfig.sectionCode j).val) = true
abbrev plane355UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane355UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane355UnusedGenConfig.deadBasis (plane355UnusedGenConfig.deadCover i)) i.val = true
abbrev plane355UnusedGenSourceProperty (i : Fin 21) : Prop :=
  forall g : Nat, g ∈ plane355UnusedGenConfig.planeBasis -> spanContainsCode (plane355UnusedGenConfig.sourceBasis i) g = true
abbrev plane355UnusedGenDeadSourceProperty (i : Fin 9) : Prop :=
  forall g : Nat, g ∈ plane355UnusedGenConfig.planeBasis -> spanContainsCode (plane355UnusedGenConfig.deadBasis i) g = true
abbrev plane355UnusedGenIndicatorProperty (i : Fin 21) : Prop :=
  forall j : Fin 22, plane355UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane355UnusedGenConfig.sourceBasis i) (plane355UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
