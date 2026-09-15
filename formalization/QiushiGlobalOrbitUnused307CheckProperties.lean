import QiushiGlobalOrbitUnused307Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane307UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 19, (plane307UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane307UnusedGenConfig.planeBasis (i.val ^^^ (plane307UnusedGenConfig.sectionCode j).val) = true
abbrev plane307UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane307UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane307UnusedGenConfig.deadBasis (plane307UnusedGenConfig.deadCover i)) i.val = true
abbrev plane307UnusedGenSourceProperty (i : Fin 20) : Prop :=
  forall g : Nat, g ∈ plane307UnusedGenConfig.planeBasis -> spanContainsCode (plane307UnusedGenConfig.sourceBasis i) g = true
abbrev plane307UnusedGenDeadSourceProperty (i : Fin 12) : Prop :=
  forall g : Nat, g ∈ plane307UnusedGenConfig.planeBasis -> spanContainsCode (plane307UnusedGenConfig.deadBasis i) g = true
abbrev plane307UnusedGenIndicatorProperty (i : Fin 20) : Prop :=
  forall j : Fin 19, plane307UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane307UnusedGenConfig.sourceBasis i) (plane307UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
