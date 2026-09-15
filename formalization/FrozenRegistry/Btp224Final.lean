import FrozenRegistry.Btp224Bool
import FrozenRegistry.Btp224Tree
import FrozenRegistry.Btp224Dispatch
import FrozenRegistry.PaddedExtraction
namespace QiushiMatmul
theorem plane224BtpGen_lb15 :
    QuotientRankAtLeast (spanCodes [302, 132, 96, 16, 1]) 15 :=
  FrozenRegistry.padded_plane_qra plane224BtpGenConfig plane224BtpGenBool
    (by intro c hc; have h := plane224BtpGenBool.hDeadCover c hc
        have hd : forall d : Fin 1, plane224BtpGenDeadBasis d = [302, 132, 96, 16, 1] := by decide +kernel
        simpa only [plane224BtpGenConfig, hd] using h)
    (0 : Fin 15) plane224BtpGenSourceQRA plane224BtpGenNoModel
end QiushiMatmul
