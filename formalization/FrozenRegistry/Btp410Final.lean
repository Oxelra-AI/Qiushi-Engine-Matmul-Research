import FrozenRegistry.Btp410Bool
import FrozenRegistry.Btp410Tree
import FrozenRegistry.Btp410Dispatch
import FrozenRegistry.PaddedExtraction
namespace QiushiMatmul
theorem plane410BtpGen_lb15 :
    QuotientRankAtLeast (spanCodes [4, 2, 1]) 15 :=
  FrozenRegistry.padded_plane_qra plane410BtpGenConfig plane410BtpGenBool
    (by intro c hc; have h := plane410BtpGenBool.hDeadCover c hc
        have hd : forall d : Fin 1, plane410BtpGenDeadBasis d = [4, 2, 1] := by decide +kernel
        simpa only [plane410BtpGenConfig, hd] using h)
    (0 : Fin 63) plane410BtpGenSourceQRA plane410BtpGenNoModel
end QiushiMatmul
