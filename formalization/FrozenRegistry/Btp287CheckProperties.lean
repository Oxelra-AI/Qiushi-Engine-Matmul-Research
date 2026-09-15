import FrozenRegistry.Btp287Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane287BtpGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 31, (plane287BtpGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane287BtpGenConfig.planeBasis (i.val ^^^ (plane287BtpGenConfig.sectionCode j).val) = true
abbrev plane287BtpGenDeadProperty (i : Fin 512) : Prop :=
  (plane287BtpGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane287BtpGenConfig.deadBasis (plane287BtpGenConfig.deadCover i)) i.val = true
abbrev plane287BtpGenSourceProperty (i : Fin 68) : Prop :=
  forall g : Nat, g ∈ plane287BtpGenConfig.planeBasis -> spanContainsCode (plane287BtpGenConfig.sourceBasis i) g = true
abbrev plane287BtpGenDeadSourceProperty (i : Fin 1) : Prop :=
  forall g : Nat, g ∈ plane287BtpGenConfig.planeBasis -> spanContainsCode (plane287BtpGenConfig.deadBasis i) g = true
abbrev plane287BtpGenIndicatorProperty (i : Fin 68) : Prop :=
  forall j : Fin 31, plane287BtpGenConfig.occSys.occCoeff i j = if spanContainsCode (plane287BtpGenConfig.sourceBasis i) (plane287BtpGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
