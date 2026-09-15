import FrozenRegistry.Btp285Data
import QiushiCertifiedTransport
import FrozenRegistry.Seed020
import QiushiFrozenRank162
import QiushiMonoOrbit126From55
import QiushiMonoOrbit97From31
import QiushiOrbit23FP
import QiushiPlane419GenBindings00
import QiushiWcOrbit51Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane285BtpGenSource0000 :
    QuotientRankAtLeast (spanCodes [96, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 8, 2, 1] [(96, 104), (20, 29), (8, 8), (2, 3), (1, 1)]
    (codeMat 273) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit97_lb15_mono

theorem plane285BtpGenSource0001 :
    QuotientRankAtLeast (spanCodes [96, 16, 10, 4, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [148, 80, 32, 12, 2, 1] [(96, 80), (16, 32), (10, 12), (4, 2), (1, 1)]
    (codeMat 273) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit51_lb14_wc

theorem plane285BtpGenSource0002 :
    QuotientRankAtLeast (spanCodes [96, 16, 8, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 16, 8, 4, 2, 1] [(96, 112), (16, 24), (8, 8), (4, 6), (2, 3), (1, 1)]
    (codeMat 273) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.FrozenRegistry.Seed020.qra12

theorem plane285BtpGenSource0003 :
    QuotientRankAtLeast (spanCodes [96, 18, 10, 6, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [148, 80, 32, 12, 2, 1] [(96, 112), (18, 45), (10, 13), (6, 3), (1, 1)]
    (codeMat 273) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit51_lb14_wc

theorem plane285BtpGenSource0004 :
    QuotientRankAtLeast (spanCodes [64, 32, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 12, 2, 1] [(64, 3), (32, 256), (20, 96), (10, 12), (1, 1)]
    (codeMat 169) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit126_lb14_mono

theorem plane285BtpGenSource0005 :
    QuotientRankAtLeast (spanCodes [64, 32, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(64, 7), (32, 128), (20, 80), (8, 2), (2, 8), (1, 1)]
    (codeMat 465) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane285BtpGenSource0006 :
    QuotientRankAtLeast (spanCodes [66, 34, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 12, 2, 1] [(66, 15), (34, 268), (20, 97), (10, 12), (1, 1)]
    (codeMat 185) (codeMat 277) (codeMat 277) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit126_lb14_mono

theorem plane285BtpGenSource0007 :
    QuotientRankAtLeast (spanCodes [68, 36, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(68, 68), (36, 32), (20, 31), (10, 10), (1, 1)]
    (codeMat 281) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane419GenBound0005

theorem plane285BtpGenSource0008 :
    QuotientRankAtLeast (spanCodes [70, 38, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(70, 69), (38, 53), (20, 30), (10, 11), (1, 1)]
    (codeMat 273) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane419GenBound0005

theorem plane285BtpGenSource0009 :
    QuotientRankAtLeast (spanCodes [128, 96, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 96, 20, 10, 1] [(128, 128), (96, 96), (20, 20), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.FrozenRank.span162_lb16

end QiushiMatmul
