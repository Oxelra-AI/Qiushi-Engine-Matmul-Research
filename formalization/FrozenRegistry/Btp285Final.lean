import FrozenRegistry.Btp285Bool
import FrozenRegistry.Btp285Tree
import FrozenRegistry.Btp285Dispatch
import FrozenRegistry.PaddedExtraction
namespace QiushiMatmul
theorem plane285BtpGen_lb17 :
    QuotientRankAtLeast (spanCodes [96, 20, 10, 1]) 17 :=
  FrozenRegistry.padded_plane_qra plane285BtpGenConfig plane285BtpGenBool
    (by intro c hc; have h := plane285BtpGenBool.hDeadCover c hc
        have hd : forall d : Fin 1, plane285BtpGenDeadBasis d = [96, 20, 10, 1] := by decide +kernel
        simpa only [plane285BtpGenConfig, hd] using h)
    (0 : Fin 31) plane285BtpGenSourceQRA plane285BtpGenNoModel
end QiushiMatmul
