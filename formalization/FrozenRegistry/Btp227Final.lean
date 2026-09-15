import FrozenRegistry.Btp227Bool
import FrozenRegistry.Btp227Tree
import FrozenRegistry.Btp227Dispatch
import FrozenRegistry.PaddedExtraction
namespace QiushiMatmul
theorem plane227BtpGen_lb15 :
    QuotientRankAtLeast (spanCodes [294, 140, 96, 16, 1]) 15 :=
  FrozenRegistry.padded_plane_qra plane227BtpGenConfig plane227BtpGenBool
    (by intro c hc; have h := plane227BtpGenBool.hDeadCover c hc
        have hd : forall d : Fin 1, plane227BtpGenDeadBasis d = [294, 140, 96, 16, 1] := by decide +kernel
        simpa only [plane227BtpGenConfig, hd] using h)
    (0 : Fin 15) plane227BtpGenSourceQRA plane227BtpGenNoModel
end QiushiMatmul
