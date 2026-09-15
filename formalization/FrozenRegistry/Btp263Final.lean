import FrozenRegistry.Btp263Bool
import FrozenRegistry.Btp263Tree
import FrozenRegistry.Btp263Dispatch
import FrozenRegistry.PaddedExtraction
namespace QiushiMatmul
theorem plane263BtpGen_lb16 :
    QuotientRankAtLeast (spanCodes [160, 12, 2, 1]) 16 :=
  FrozenRegistry.padded_plane_qra plane263BtpGenConfig plane263BtpGenBool
    (by intro c hc; have h := plane263BtpGenBool.hDeadCover c hc
        have hd : forall d : Fin 1, plane263BtpGenDeadBasis d = [160, 12, 2, 1] := by decide +kernel
        simpa only [plane263BtpGenConfig, hd] using h)
    (0 : Fin 31) plane263BtpGenSourceQRA plane263BtpGenNoModel
end QiushiMatmul
