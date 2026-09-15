import FrozenRegistry.Btp265Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane265BtpGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 31, (plane265BtpGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane265BtpGenConfig.planeBasis (i.val ^^^ (plane265BtpGenConfig.sectionCode j).val) = true
abbrev plane265BtpGenDeadProperty (i : Fin 512) : Prop :=
  (plane265BtpGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane265BtpGenConfig.deadBasis (plane265BtpGenConfig.deadCover i)) i.val = true
abbrev plane265BtpGenSourceProperty (i : Fin 31) : Prop :=
  forall g : Nat, g ∈ plane265BtpGenConfig.planeBasis -> spanContainsCode (plane265BtpGenConfig.sourceBasis i) g = true
abbrev plane265BtpGenDeadSourceProperty (i : Fin 1) : Prop :=
  forall g : Nat, g ∈ plane265BtpGenConfig.planeBasis -> spanContainsCode (plane265BtpGenConfig.deadBasis i) g = true
abbrev plane265BtpGenIndicatorProperty (i : Fin 31) : Prop :=
  forall j : Fin 31, plane265BtpGenConfig.occSys.occCoeff i j = if spanContainsCode (plane265BtpGenConfig.sourceBasis i) (plane265BtpGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
