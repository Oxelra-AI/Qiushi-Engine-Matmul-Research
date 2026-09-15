import FrozenRegistry.Btp260Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane260BtpGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 31, (plane260BtpGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane260BtpGenConfig.planeBasis (i.val ^^^ (plane260BtpGenConfig.sectionCode j).val) = true
abbrev plane260BtpGenDeadProperty (i : Fin 512) : Prop :=
  (plane260BtpGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane260BtpGenConfig.deadBasis (plane260BtpGenConfig.deadCover i)) i.val = true
abbrev plane260BtpGenSourceProperty (i : Fin 33) : Prop :=
  forall g : Nat, g ∈ plane260BtpGenConfig.planeBasis -> spanContainsCode (plane260BtpGenConfig.sourceBasis i) g = true
abbrev plane260BtpGenDeadSourceProperty (i : Fin 1) : Prop :=
  forall g : Nat, g ∈ plane260BtpGenConfig.planeBasis -> spanContainsCode (plane260BtpGenConfig.deadBasis i) g = true
abbrev plane260BtpGenIndicatorProperty (i : Fin 33) : Prop :=
  forall j : Fin 31, plane260BtpGenConfig.occSys.occCoeff i j = if spanContainsCode (plane260BtpGenConfig.sourceBasis i) (plane260BtpGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
