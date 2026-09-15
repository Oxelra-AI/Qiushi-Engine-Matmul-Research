import QiushiPlane471LowerGenData
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane471LowerGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 6, (plane471LowerGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane471LowerGenConfig.planeBasis (i.val ^^^ (plane471LowerGenConfig.sectionCode j).val) = true
abbrev plane471LowerGenDeadProperty (i : Fin 512) : Prop :=
  (plane471LowerGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane471LowerGenConfig.deadBasis (plane471LowerGenConfig.deadCover i)) i.val = true
abbrev plane471LowerGenSourceProperty (i : Fin 53) : Prop :=
  forall g : Nat, g ∈ plane471LowerGenConfig.planeBasis -> spanContainsCode (plane471LowerGenConfig.sourceBasis i) g = true
abbrev plane471LowerGenDeadSourceProperty (i : Fin 49) : Prop :=
  forall g : Nat, g ∈ plane471LowerGenConfig.planeBasis -> spanContainsCode (plane471LowerGenConfig.deadBasis i) g = true
abbrev plane471LowerGenIndicatorProperty (i : Fin 53) : Prop :=
  forall j : Fin 6, plane471LowerGenConfig.occSys.occCoeff i j = if spanContainsCode (plane471LowerGenConfig.sourceBasis i) (plane471LowerGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
