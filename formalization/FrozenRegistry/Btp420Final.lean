import FrozenRegistry.Btp420Bool
import FrozenRegistry.Btp420Tree
import FrozenRegistry.Btp420Dispatch
import FrozenRegistry.PaddedExtraction
namespace QiushiMatmul
theorem plane420BtpGen_lb18 :
    QuotientRankAtLeast (spanCodes [68, 10, 1]) 18 :=
  FrozenRegistry.padded_plane_qra plane420BtpGenConfig plane420BtpGenBool
    (by intro c hc; have h := plane420BtpGenBool.hDeadCover c hc
        have hd : forall d : Fin 1, plane420BtpGenDeadBasis d = [68, 10, 1] := by decide +kernel
        simpa only [plane420BtpGenConfig, hd] using h)
    (0 : Fin 63) plane420BtpGenSourceQRA plane420BtpGenNoModel
end QiushiMatmul
