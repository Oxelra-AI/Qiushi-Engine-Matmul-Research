import QiushiPlane463LowerGenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane463LowerGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 6, (plane463LowerGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane463LowerGenConfig.planeBasis (i.val ^^^ (plane463LowerGenConfig.sectionCode j).val) = true
abbrev plane463LowerGenDeadProperty (i : Fin 512) : Prop :=
  (plane463LowerGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane463LowerGenConfig.deadBasis (plane463LowerGenConfig.deadCover i)) i.val = true
abbrev plane463LowerGenSourceProperty (i : Fin 49) : Prop :=
  forall g : Nat, g ∈ plane463LowerGenConfig.planeBasis -> spanContainsCode (plane463LowerGenConfig.sourceBasis i) g = true
abbrev plane463LowerGenDeadSourceProperty (i : Fin 45) : Prop :=
  forall g : Nat, g ∈ plane463LowerGenConfig.planeBasis -> spanContainsCode (plane463LowerGenConfig.deadBasis i) g = true
abbrev plane463LowerGenIndicatorProperty (i : Fin 49) : Prop :=
  forall j : Fin 6, plane463LowerGenConfig.occSys.occCoeff i j = if spanContainsCode (plane463LowerGenConfig.sourceBasis i) (plane463LowerGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
