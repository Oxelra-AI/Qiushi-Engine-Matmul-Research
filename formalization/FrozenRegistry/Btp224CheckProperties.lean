import FrozenRegistry.Btp224Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane224BtpGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 15, (plane224BtpGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane224BtpGenConfig.planeBasis (i.val ^^^ (plane224BtpGenConfig.sectionCode j).val) = true
abbrev plane224BtpGenDeadProperty (i : Fin 512) : Prop :=
  (plane224BtpGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane224BtpGenConfig.deadBasis (plane224BtpGenConfig.deadCover i)) i.val = true
abbrev plane224BtpGenSourceProperty (i : Fin 15) : Prop :=
  forall g : Nat, g ∈ plane224BtpGenConfig.planeBasis -> spanContainsCode (plane224BtpGenConfig.sourceBasis i) g = true
abbrev plane224BtpGenDeadSourceProperty (i : Fin 1) : Prop :=
  forall g : Nat, g ∈ plane224BtpGenConfig.planeBasis -> spanContainsCode (plane224BtpGenConfig.deadBasis i) g = true
abbrev plane224BtpGenIndicatorProperty (i : Fin 15) : Prop :=
  forall j : Fin 15, plane224BtpGenConfig.occSys.occCoeff i j = if spanContainsCode (plane224BtpGenConfig.sourceBasis i) (plane224BtpGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
