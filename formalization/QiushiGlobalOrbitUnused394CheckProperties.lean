import QiushiGlobalOrbitUnused394Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane394UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 9, (plane394UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane394UnusedGenConfig.planeBasis (i.val ^^^ (plane394UnusedGenConfig.sectionCode j).val) = true
abbrev plane394UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane394UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane394UnusedGenConfig.deadBasis (plane394UnusedGenConfig.deadCover i)) i.val = true
abbrev plane394UnusedGenSourceProperty (i : Fin 32) : Prop :=
  forall g : Nat, g ∈ plane394UnusedGenConfig.planeBasis -> spanContainsCode (plane394UnusedGenConfig.sourceBasis i) g = true
abbrev plane394UnusedGenDeadSourceProperty (i : Fin 25) : Prop :=
  forall g : Nat, g ∈ plane394UnusedGenConfig.planeBasis -> spanContainsCode (plane394UnusedGenConfig.deadBasis i) g = true
abbrev plane394UnusedGenIndicatorProperty (i : Fin 32) : Prop :=
  forall j : Fin 9, plane394UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane394UnusedGenConfig.sourceBasis i) (plane394UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
