import QiushiGlobalOrbitUnused398Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane398UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 17, (plane398UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane398UnusedGenConfig.planeBasis (i.val ^^^ (plane398UnusedGenConfig.sectionCode j).val) = true
abbrev plane398UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane398UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane398UnusedGenConfig.deadBasis (plane398UnusedGenConfig.deadCover i)) i.val = true
abbrev plane398UnusedGenSourceProperty (i : Fin 25) : Prop :=
  forall g : Nat, g ∈ plane398UnusedGenConfig.planeBasis -> spanContainsCode (plane398UnusedGenConfig.sourceBasis i) g = true
abbrev plane398UnusedGenDeadSourceProperty (i : Fin 14) : Prop :=
  forall g : Nat, g ∈ plane398UnusedGenConfig.planeBasis -> spanContainsCode (plane398UnusedGenConfig.deadBasis i) g = true
abbrev plane398UnusedGenIndicatorProperty (i : Fin 25) : Prop :=
  forall j : Fin 17, plane398UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane398UnusedGenConfig.sourceBasis i) (plane398UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
