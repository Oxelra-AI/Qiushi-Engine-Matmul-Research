import FrozenRegistry.Btp263Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane263BtpGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 31, (plane263BtpGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane263BtpGenConfig.planeBasis (i.val ^^^ (plane263BtpGenConfig.sectionCode j).val) = true
abbrev plane263BtpGenDeadProperty (i : Fin 512) : Prop :=
  (plane263BtpGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane263BtpGenConfig.deadBasis (plane263BtpGenConfig.deadCover i)) i.val = true
abbrev plane263BtpGenSourceProperty (i : Fin 31) : Prop :=
  forall g : Nat, g ∈ plane263BtpGenConfig.planeBasis -> spanContainsCode (plane263BtpGenConfig.sourceBasis i) g = true
abbrev plane263BtpGenDeadSourceProperty (i : Fin 1) : Prop :=
  forall g : Nat, g ∈ plane263BtpGenConfig.planeBasis -> spanContainsCode (plane263BtpGenConfig.deadBasis i) g = true
abbrev plane263BtpGenIndicatorProperty (i : Fin 31) : Prop :=
  forall j : Fin 31, plane263BtpGenConfig.occSys.occCoeff i j = if spanContainsCode (plane263BtpGenConfig.sourceBasis i) (plane263BtpGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
