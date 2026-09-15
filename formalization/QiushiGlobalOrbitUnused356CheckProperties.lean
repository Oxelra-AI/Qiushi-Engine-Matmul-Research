import QiushiGlobalOrbitUnused356Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane356UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 20, (plane356UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane356UnusedGenConfig.planeBasis (i.val ^^^ (plane356UnusedGenConfig.sectionCode j).val) = true
abbrev plane356UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane356UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane356UnusedGenConfig.deadBasis (plane356UnusedGenConfig.deadCover i)) i.val = true
abbrev plane356UnusedGenSourceProperty (i : Fin 27) : Prop :=
  forall g : Nat, g ∈ plane356UnusedGenConfig.planeBasis -> spanContainsCode (plane356UnusedGenConfig.sourceBasis i) g = true
abbrev plane356UnusedGenDeadSourceProperty (i : Fin 11) : Prop :=
  forall g : Nat, g ∈ plane356UnusedGenConfig.planeBasis -> spanContainsCode (plane356UnusedGenConfig.deadBasis i) g = true
abbrev plane356UnusedGenIndicatorProperty (i : Fin 27) : Prop :=
  forall j : Fin 20, plane356UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane356UnusedGenConfig.sourceBasis i) (plane356UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
