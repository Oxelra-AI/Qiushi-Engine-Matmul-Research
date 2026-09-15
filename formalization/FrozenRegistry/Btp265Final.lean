import FrozenRegistry.Btp265Bool
import FrozenRegistry.Btp265Tree
import FrozenRegistry.Btp265Dispatch
import FrozenRegistry.PaddedExtraction
namespace QiushiMatmul
theorem plane265BtpGen_lb16 :
    QuotientRankAtLeast (spanCodes [272, 12, 2, 1]) 16 :=
  FrozenRegistry.padded_plane_qra plane265BtpGenConfig plane265BtpGenBool
    (by intro c hc; have h := plane265BtpGenBool.hDeadCover c hc
        have hd : forall d : Fin 1, plane265BtpGenDeadBasis d = [272, 12, 2, 1] := by decide +kernel
        simpa only [plane265BtpGenConfig, hd] using h)
    (0 : Fin 31) plane265BtpGenSourceQRA plane265BtpGenNoModel
end QiushiMatmul
