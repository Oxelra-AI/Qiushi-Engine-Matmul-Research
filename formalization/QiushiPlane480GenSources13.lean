import QiushiPlane480GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit252From101
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane480GenSource0130 :
    QuotientRankAtLeast (spanCodes [32, 16, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 8, 2, 1] [(32, 2), (16, 1), (2, 8), (1, 32)]
    (codeMat 266) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit252_lb15_mono

theorem plane480GenSource0131 :
    QuotientRankAtLeast (spanCodes [32, 16, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 8, 2, 1] [(32, 1), (16, 2), (4, 8), (1, 32)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit252_lb15_mono

theorem plane480GenSource0132 :
    QuotientRankAtLeast (spanCodes [32, 16, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 8, 2, 1] [(32, 2), (16, 3), (6, 8), (1, 32)]
    (codeMat 266) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit252_lb15_mono

theorem plane480GenSource0133 :
    QuotientRankAtLeast (spanCodes [40, 16, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 8, 2, 1] [(40, 2), (16, 1), (2, 8), (1, 32)]
    (codeMat 266) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit252_lb15_mono

theorem plane480GenSource0134 :
    QuotientRankAtLeast (spanCodes [40, 16, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 8, 2, 1] [(40, 1), (16, 2), (4, 32), (1, 40)]
    (codeMat 266) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit252_lb15_mono

theorem plane480GenSource0135 :
    QuotientRankAtLeast (spanCodes [40, 16, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 8, 2, 1] [(40, 3), (16, 2), (6, 32), (1, 40)]
    (codeMat 266) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit252_lb15_mono

theorem plane480GenSource0136 :
    QuotientRankAtLeast (spanCodes [64, 16, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 8, 2, 1] [(64, 2), (16, 32), (2, 8), (1, 1)]
    (codeMat 161) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit252_lb15_mono

theorem plane480GenSource0137 :
    QuotientRankAtLeast (spanCodes [72, 16, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 8, 2, 1] [(72, 2), (16, 32), (2, 8), (1, 1)]
    (codeMat 177) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit252_lb15_mono

theorem plane480GenSource0138 :
    QuotientRankAtLeast (spanCodes [128, 16, 8, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 8, 2, 1] [(128, 2), (16, 1), (8, 8), (1, 32)]
    (codeMat 98) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit252_lb15_mono

theorem plane480GenSource0139 :
    QuotientRankAtLeast (spanCodes [130, 16, 8, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 8, 2, 1] [(130, 2), (16, 1), (8, 8), (1, 32)]
    (codeMat 106) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit252_lb15_mono

end QiushiMatmul
