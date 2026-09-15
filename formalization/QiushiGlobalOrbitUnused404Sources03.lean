import QiushiGlobalOrbitUnused404Data
import QiushiCertifiedTransport
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane404UnusedGenSource0030 :
    QuotientRankAtLeast (spanCodes [259, 128, 66, 34, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 413), (128, 9), (66, 126), (34, 129), (18, 1), (10, 385), (6, 130)]
    (codeMat 187) (codeMat 111) (codeMat 412) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
