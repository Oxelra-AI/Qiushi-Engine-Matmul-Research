import QiushiGlobalOrbitUnused339Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane339UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 7, (plane339UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane339UnusedGenConfig.planeBasis (i.val ^^^ (plane339UnusedGenConfig.sectionCode j).val) = true
abbrev plane339UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane339UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane339UnusedGenConfig.deadBasis (plane339UnusedGenConfig.deadCover i)) i.val = true
abbrev plane339UnusedGenSourceProperty (i : Fin 31) : Prop :=
  forall g : Nat, g ∈ plane339UnusedGenConfig.planeBasis -> spanContainsCode (plane339UnusedGenConfig.sourceBasis i) g = true
abbrev plane339UnusedGenDeadSourceProperty (i : Fin 28) : Prop :=
  forall g : Nat, g ∈ plane339UnusedGenConfig.planeBasis -> spanContainsCode (plane339UnusedGenConfig.deadBasis i) g = true
abbrev plane339UnusedGenIndicatorProperty (i : Fin 31) : Prop :=
  forall j : Fin 7, plane339UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane339UnusedGenConfig.sourceBasis i) (plane339UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
