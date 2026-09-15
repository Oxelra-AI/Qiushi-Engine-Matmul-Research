import QiushiGlobalOrbitUnused321Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane321UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 26, (plane321UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane321UnusedGenConfig.planeBasis (i.val ^^^ (plane321UnusedGenConfig.sectionCode j).val) = true
abbrev plane321UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane321UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane321UnusedGenConfig.deadBasis (plane321UnusedGenConfig.deadCover i)) i.val = true
abbrev plane321UnusedGenSourceProperty (i : Fin 49) : Prop :=
  forall g : Nat, g ∈ plane321UnusedGenConfig.planeBasis -> spanContainsCode (plane321UnusedGenConfig.sourceBasis i) g = true
abbrev plane321UnusedGenDeadSourceProperty (i : Fin 5) : Prop :=
  forall g : Nat, g ∈ plane321UnusedGenConfig.planeBasis -> spanContainsCode (plane321UnusedGenConfig.deadBasis i) g = true
abbrev plane321UnusedGenIndicatorProperty (i : Fin 49) : Prop :=
  forall j : Fin 26, plane321UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane321UnusedGenConfig.sourceBasis i) (plane321UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
