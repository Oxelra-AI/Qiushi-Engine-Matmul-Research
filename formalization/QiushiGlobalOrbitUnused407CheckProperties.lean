import QiushiGlobalOrbitUnused407Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane407UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 12, (plane407UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane407UnusedGenConfig.planeBasis (i.val ^^^ (plane407UnusedGenConfig.sectionCode j).val) = true
abbrev plane407UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane407UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane407UnusedGenConfig.deadBasis (plane407UnusedGenConfig.deadCover i)) i.val = true
abbrev plane407UnusedGenSourceProperty (i : Fin 25) : Prop :=
  forall g : Nat, g ∈ plane407UnusedGenConfig.planeBasis -> spanContainsCode (plane407UnusedGenConfig.sourceBasis i) g = true
abbrev plane407UnusedGenDeadSourceProperty (i : Fin 19) : Prop :=
  forall g : Nat, g ∈ plane407UnusedGenConfig.planeBasis -> spanContainsCode (plane407UnusedGenConfig.deadBasis i) g = true
abbrev plane407UnusedGenIndicatorProperty (i : Fin 25) : Prop :=
  forall j : Fin 12, plane407UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane407UnusedGenConfig.sourceBasis i) (plane407UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
