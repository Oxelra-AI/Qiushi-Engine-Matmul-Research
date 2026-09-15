import QiushiPlane456LowerGenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane456LowerGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 3, (plane456LowerGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane456LowerGenConfig.planeBasis (i.val ^^^ (plane456LowerGenConfig.sectionCode j).val) = true
abbrev plane456LowerGenDeadProperty (i : Fin 512) : Prop :=
  (plane456LowerGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane456LowerGenConfig.deadBasis (plane456LowerGenConfig.deadCover i)) i.val = true
abbrev plane456LowerGenSourceProperty (i : Fin 50) : Prop :=
  forall g : Nat, g ∈ plane456LowerGenConfig.planeBasis -> spanContainsCode (plane456LowerGenConfig.sourceBasis i) g = true
abbrev plane456LowerGenDeadSourceProperty (i : Fin 49) : Prop :=
  forall g : Nat, g ∈ plane456LowerGenConfig.planeBasis -> spanContainsCode (plane456LowerGenConfig.deadBasis i) g = true
abbrev plane456LowerGenIndicatorProperty (i : Fin 50) : Prop :=
  forall j : Fin 3, plane456LowerGenConfig.occSys.occCoeff i j = if spanContainsCode (plane456LowerGenConfig.sourceBasis i) (plane456LowerGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
