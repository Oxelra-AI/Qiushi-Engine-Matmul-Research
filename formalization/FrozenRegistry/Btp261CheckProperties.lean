import FrozenRegistry.Btp261Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane261BtpGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 31, (plane261BtpGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane261BtpGenConfig.planeBasis (i.val ^^^ (plane261BtpGenConfig.sectionCode j).val) = true
abbrev plane261BtpGenDeadProperty (i : Fin 512) : Prop :=
  (plane261BtpGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane261BtpGenConfig.deadBasis (plane261BtpGenConfig.deadCover i)) i.val = true
abbrev plane261BtpGenSourceProperty (i : Fin 34) : Prop :=
  forall g : Nat, g ∈ plane261BtpGenConfig.planeBasis -> spanContainsCode (plane261BtpGenConfig.sourceBasis i) g = true
abbrev plane261BtpGenDeadSourceProperty (i : Fin 1) : Prop :=
  forall g : Nat, g ∈ plane261BtpGenConfig.planeBasis -> spanContainsCode (plane261BtpGenConfig.deadBasis i) g = true
abbrev plane261BtpGenIndicatorProperty (i : Fin 34) : Prop :=
  forall j : Fin 31, plane261BtpGenConfig.occSys.occCoeff i j = if spanContainsCode (plane261BtpGenConfig.sourceBasis i) (plane261BtpGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
