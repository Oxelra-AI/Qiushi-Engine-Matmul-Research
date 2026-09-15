import FrozenRegistry.Btp287Bool
import FrozenRegistry.Btp287Tree
import FrozenRegistry.Btp287Dispatch
import FrozenRegistry.PaddedExtraction
namespace QiushiMatmul
theorem plane287BtpGen_lb17 :
    QuotientRankAtLeast (spanCodes [160, 20, 10, 1]) 17 :=
  FrozenRegistry.padded_plane_qra plane287BtpGenConfig plane287BtpGenBool
    (by intro c hc; have h := plane287BtpGenBool.hDeadCover c hc
        have hd : forall d : Fin 1, plane287BtpGenDeadBasis d = [160, 20, 10, 1] := by decide +kernel
        simpa only [plane287BtpGenConfig, hd] using h)
    (0 : Fin 31) plane287BtpGenSourceQRA plane287BtpGenNoModel
end QiushiMatmul
