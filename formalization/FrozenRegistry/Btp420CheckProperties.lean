import FrozenRegistry.Btp420Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane420BtpGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 63, (plane420BtpGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane420BtpGenConfig.planeBasis (i.val ^^^ (plane420BtpGenConfig.sectionCode j).val) = true
abbrev plane420BtpGenDeadProperty (i : Fin 512) : Prop :=
  (plane420BtpGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane420BtpGenConfig.deadBasis (plane420BtpGenConfig.deadCover i)) i.val = true
abbrev plane420BtpGenSourceProperty (i : Fin 63) : Prop :=
  forall g : Nat, g ∈ plane420BtpGenConfig.planeBasis -> spanContainsCode (plane420BtpGenConfig.sourceBasis i) g = true
abbrev plane420BtpGenDeadSourceProperty (i : Fin 1) : Prop :=
  forall g : Nat, g ∈ plane420BtpGenConfig.planeBasis -> spanContainsCode (plane420BtpGenConfig.deadBasis i) g = true
abbrev plane420BtpGenIndicatorProperty (i : Fin 63) : Prop :=
  forall j : Fin 63, plane420BtpGenConfig.occSys.occCoeff i j = if spanContainsCode (plane420BtpGenConfig.sourceBasis i) (plane420BtpGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
