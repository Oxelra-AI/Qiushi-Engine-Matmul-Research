import FrozenRegistry.Btp285Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane285BtpGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 31, (plane285BtpGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane285BtpGenConfig.planeBasis (i.val ^^^ (plane285BtpGenConfig.sectionCode j).val) = true
abbrev plane285BtpGenDeadProperty (i : Fin 512) : Prop :=
  (plane285BtpGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane285BtpGenConfig.deadBasis (plane285BtpGenConfig.deadCover i)) i.val = true
abbrev plane285BtpGenSourceProperty (i : Fin 39) : Prop :=
  forall g : Nat, g ∈ plane285BtpGenConfig.planeBasis -> spanContainsCode (plane285BtpGenConfig.sourceBasis i) g = true
abbrev plane285BtpGenDeadSourceProperty (i : Fin 1) : Prop :=
  forall g : Nat, g ∈ plane285BtpGenConfig.planeBasis -> spanContainsCode (plane285BtpGenConfig.deadBasis i) g = true
abbrev plane285BtpGenIndicatorProperty (i : Fin 39) : Prop :=
  forall j : Fin 31, plane285BtpGenConfig.occSys.occCoeff i j = if spanContainsCode (plane285BtpGenConfig.sourceBasis i) (plane285BtpGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
