import QiushiGlobalOrbitUnused408Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane408UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 18, (plane408UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane408UnusedGenConfig.planeBasis (i.val ^^^ (plane408UnusedGenConfig.sectionCode j).val) = true
abbrev plane408UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane408UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane408UnusedGenConfig.deadBasis (plane408UnusedGenConfig.deadCover i)) i.val = true
abbrev plane408UnusedGenSourceProperty (i : Fin 25) : Prop :=
  forall g : Nat, g ∈ plane408UnusedGenConfig.planeBasis -> spanContainsCode (plane408UnusedGenConfig.sourceBasis i) g = true
abbrev plane408UnusedGenDeadSourceProperty (i : Fin 13) : Prop :=
  forall g : Nat, g ∈ plane408UnusedGenConfig.planeBasis -> spanContainsCode (plane408UnusedGenConfig.deadBasis i) g = true
abbrev plane408UnusedGenIndicatorProperty (i : Fin 25) : Prop :=
  forall j : Fin 18, plane408UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane408UnusedGenConfig.sourceBasis i) (plane408UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
