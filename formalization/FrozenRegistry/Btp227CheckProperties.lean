import FrozenRegistry.Btp227Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane227BtpGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 15, (plane227BtpGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane227BtpGenConfig.planeBasis (i.val ^^^ (plane227BtpGenConfig.sectionCode j).val) = true
abbrev plane227BtpGenDeadProperty (i : Fin 512) : Prop :=
  (plane227BtpGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane227BtpGenConfig.deadBasis (plane227BtpGenConfig.deadCover i)) i.val = true
abbrev plane227BtpGenSourceProperty (i : Fin 15) : Prop :=
  forall g : Nat, g ∈ plane227BtpGenConfig.planeBasis -> spanContainsCode (plane227BtpGenConfig.sourceBasis i) g = true
abbrev plane227BtpGenDeadSourceProperty (i : Fin 1) : Prop :=
  forall g : Nat, g ∈ plane227BtpGenConfig.planeBasis -> spanContainsCode (plane227BtpGenConfig.deadBasis i) g = true
abbrev plane227BtpGenIndicatorProperty (i : Fin 15) : Prop :=
  forall j : Fin 15, plane227BtpGenConfig.occSys.occCoeff i j = if spanContainsCode (plane227BtpGenConfig.sourceBasis i) (plane227BtpGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
