import QiushiPlane425GenData
import QiushiCertifiedTransport
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane425GenSource0150 :
    QuotientRankAtLeast (spanCodes [258, 144, 82, 32, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 385), (144, 511), (82, 252), (32, 8), (10, 480), (6, 384), (1, 256)]
    (codeMat 85) (codeMat 214) (codeMat 214) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane425GenSource0151 :
    QuotientRankAtLeast (spanCodes [258, 144, 80, 34, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 137), (144, 3), (80, 508), (34, 136), (10, 480), (6, 128), (1, 256)]
    (codeMat 94) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane425GenSource0152 :
    QuotientRankAtLeast (spanCodes [258, 144, 66, 48, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 510), (144, 384), (66, 150), (48, 8), (10, 22), (6, 1), (1, 2)]
    (codeMat 401) (codeMat 444) (codeMat 110) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane425GenSource0153 :
    QuotientRankAtLeast (spanCodes [258, 128, 80, 50, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 362), (128, 511), (80, 227), (50, 23), (10, 31), (6, 2), (1, 3)]
    (codeMat 465) (codeMat 415) (codeMat 253) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane425GenSource0154 :
    QuotientRankAtLeast (spanCodes [258, 130, 82, 50, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 258), (130, 384), (82, 245), (50, 22), (10, 30), (6, 2), (1, 3)]
    (codeMat 337) (codeMat 409) (codeMat 473) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane425GenSource0155 :
    QuotientRankAtLeast (spanCodes [258, 146, 80, 34, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 385), (146, 511), (80, 252), (34, 392), (10, 224), (6, 384), (1, 256)]
    (codeMat 93) (codeMat 214) (codeMat 214) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane425GenSource0156 :
    QuotientRankAtLeast (spanCodes [258, 146, 82, 32, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 137), (146, 3), (82, 508), (32, 8), (10, 224), (6, 128), (1, 256)]
    (codeMat 87) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane425GenSource0157 :
    QuotientRankAtLeast (spanCodes [258, 128, 82, 50, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 509), (128, 360), (82, 245), (50, 21), (10, 29), (6, 2), (1, 3)]
    (codeMat 401) (codeMat 431) (codeMat 477) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane425GenSource0158 :
    QuotientRankAtLeast (spanCodes [258, 130, 80, 50, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 386), (130, 256), (80, 227), (50, 20), (10, 28), (6, 2), (1, 3)]
    (codeMat 337) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane425GenSource0159 :
    QuotientRankAtLeast (spanCodes [258, 146, 66, 48, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 361), (146, 256), (66, 150), (48, 8), (10, 20), (6, 1), (1, 2)]
    (codeMat 465) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
