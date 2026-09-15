import FrozenRegistry.Btp410Data
import QiushiFiniteBlocks
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
abbrev plane410BtpGenSectionProperty (i : Fin 512) : Prop :=
  forall j : Fin 63, (plane410BtpGenConfig.classifyCode i).val = j.val + 1 -> spanContainsCode plane410BtpGenConfig.planeBasis (i.val ^^^ (plane410BtpGenConfig.sectionCode j).val) = true
abbrev plane410BtpGenDeadProperty (i : Fin 512) : Prop :=
  (plane410BtpGenConfig.classifyCode i).val = 0 -> spanContainsCode (plane410BtpGenConfig.deadBasis (plane410BtpGenConfig.deadCover i)) i.val = true
abbrev plane410BtpGenSourceProperty (i : Fin 63) : Prop :=
  forall g : Nat, g ∈ plane410BtpGenConfig.planeBasis -> spanContainsCode (plane410BtpGenConfig.sourceBasis i) g = true
abbrev plane410BtpGenDeadSourceProperty (i : Fin 1) : Prop :=
  forall g : Nat, g ∈ plane410BtpGenConfig.planeBasis -> spanContainsCode (plane410BtpGenConfig.deadBasis i) g = true
abbrev plane410BtpGenIndicatorProperty (i : Fin 63) : Prop :=
  forall j : Fin 63, plane410BtpGenConfig.occSys.occCoeff i j = if spanContainsCode (plane410BtpGenConfig.sourceBasis i) (plane410BtpGenConfig.sectionCode j).val then 1 else 0
end QiushiMatmul
