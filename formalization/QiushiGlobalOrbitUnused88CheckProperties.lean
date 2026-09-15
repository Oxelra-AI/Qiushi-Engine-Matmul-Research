import QiushiGlobalOrbitUnused88Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane88UnusedGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 3, (plane88UnusedGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane88UnusedGenConfig.planeBasis (i.val ^^^ (plane88UnusedGenConfig.sectionCode j).val) = true
abbrev plane88UnusedGenDeadProperty (i : Fin 512) : Prop :=
  (plane88UnusedGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane88UnusedGenConfig.deadBasis (plane88UnusedGenConfig.deadCover i)) i.val = true
abbrev plane88UnusedGenSourceProperty (i : Fin 13) : Prop :=
  forall g : Nat, g ∈ plane88UnusedGenConfig.planeBasis -> spanContainsCode (plane88UnusedGenConfig.sourceBasis i) g = true
abbrev plane88UnusedGenDeadSourceProperty (i : Fin 12) : Prop :=
  forall g : Nat, g ∈ plane88UnusedGenConfig.planeBasis -> spanContainsCode (plane88UnusedGenConfig.deadBasis i) g = true
abbrev plane88UnusedGenIndicatorProperty (i : Fin 13) : Prop :=
  forall j : Fin 3, plane88UnusedGenConfig.occSys.occCoeff i j = if spanContainsCode (plane88UnusedGenConfig.sourceBasis i) (plane88UnusedGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
