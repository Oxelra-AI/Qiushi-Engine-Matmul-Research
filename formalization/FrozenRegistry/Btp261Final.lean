import FrozenRegistry.Btp261Bool
import FrozenRegistry.Btp261Tree
import FrozenRegistry.Btp261Dispatch
import FrozenRegistry.PaddedExtraction
namespace QiushiMatmul
theorem plane261BtpGen_lb16 :
    QuotientRankAtLeast (spanCodes [96, 12, 2, 1]) 16 :=
  FrozenRegistry.padded_plane_qra plane261BtpGenConfig plane261BtpGenBool
    (by intro c hc; have h := plane261BtpGenBool.hDeadCover c hc
        have hd : forall d : Fin 1, plane261BtpGenDeadBasis d = [96, 12, 2, 1] := by decide +kernel
        simpa only [plane261BtpGenConfig, hd] using h)
    (0 : Fin 31) plane261BtpGenSourceQRA plane261BtpGenNoModel
end QiushiMatmul
