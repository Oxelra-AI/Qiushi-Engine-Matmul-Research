import QiushiGlobalOrbitUnused240Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane240UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 9, (plane240UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane240UnusedGenConfig.planeBasis (i.val ^^^ (plane240UnusedGenConfig.sectionCode j).val) = true
abbrev plane240UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane240UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane240UnusedGenConfig.deadBasis (plane240UnusedGenConfig.deadCover i)) i.val = true
abbrev plane240UnusedGenSourceProperty (i : Fin 15) : Prop :=
  forall g : Nat, g ∈ plane240UnusedGenConfig.planeBasis -> spanContainsCode (plane240UnusedGenConfig.sourceBasis i) g = true
abbrev plane240UnusedGenDeadSourceProperty (i : Fin 6) : Prop :=
  forall g : Nat, g ∈ plane240UnusedGenConfig.planeBasis -> spanContainsCode (plane240UnusedGenConfig.deadBasis i) g = true
abbrev plane240UnusedGenIndicatorProperty (i : Fin 15) : Prop :=
  forall j : Fin 9, plane240UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane240UnusedGenConfig.sourceBasis i) (plane240UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
