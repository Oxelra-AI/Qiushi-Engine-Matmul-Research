import FrozenRegistry.Btp260Bool
import FrozenRegistry.Btp260Tree
import FrozenRegistry.Btp260Dispatch
import FrozenRegistry.PaddedExtraction
namespace QiushiMatmul
theorem plane260BtpGen_lb16 :
    QuotientRankAtLeast (spanCodes [80, 12, 2, 1]) 16 :=
  FrozenRegistry.padded_plane_qra plane260BtpGenConfig plane260BtpGenBool
    (by intro c hc; have h := plane260BtpGenBool.hDeadCover c hc
        have hd : forall d : Fin 1, plane260BtpGenDeadBasis d = [80, 12, 2, 1] := by decide +kernel
        simpa only [plane260BtpGenConfig, hd] using h)
    (0 : Fin 31) plane260BtpGenSourceQRA plane260BtpGenNoModel
end QiushiMatmul
