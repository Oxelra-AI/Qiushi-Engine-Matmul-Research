import QiushiPlane470LowerGenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane470LowerGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 5, (plane470LowerGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane470LowerGenConfig.planeBasis (i.val ^^^ (plane470LowerGenConfig.sectionCode j).val) = true
abbrev plane470LowerGenDeadProperty (i : Fin 512) : Prop :=
  (plane470LowerGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane470LowerGenConfig.deadBasis (plane470LowerGenConfig.deadCover i)) i.val = true
abbrev plane470LowerGenSourceProperty (i : Fin 52) : Prop :=
  forall g : Nat, g ∈ plane470LowerGenConfig.planeBasis -> spanContainsCode (plane470LowerGenConfig.sourceBasis i) g = true
abbrev plane470LowerGenDeadSourceProperty (i : Fin 50) : Prop :=
  forall g : Nat, g ∈ plane470LowerGenConfig.planeBasis -> spanContainsCode (plane470LowerGenConfig.deadBasis i) g = true
abbrev plane470LowerGenIndicatorProperty (i : Fin 52) : Prop :=
  forall j : Fin 5, plane470LowerGenConfig.occSys.occCoeff i j = if spanContainsCode (plane470LowerGenConfig.sourceBasis i) (plane470LowerGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
