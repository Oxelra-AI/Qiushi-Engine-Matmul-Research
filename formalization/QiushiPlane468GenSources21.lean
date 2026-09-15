import QiushiPlane468GenData
import QiushiCertifiedTransport
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane468GenSource0210 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 35, 17, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 128), (128, 256), (66, 480), (35, 10), (17, 28), (10, 31), (7, 8)]
    (codeMat 267) (codeMat 233) (codeMat 233) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane468GenSource0211 :
    QuotientRankAtLeast (spanCodes [259, 130, 67, 33, 16, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 508), (130, 2), (67, 148), (33, 373), (16, 130), (10, 276), (7, 511)]
    (codeMat 477) (codeMat 124) (codeMat 124) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane468GenSource0212 :
    QuotientRankAtLeast (spanCodes [258, 130, 67, 32, 17, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 10), (130, 3), (67, 28), (32, 130), (17, 227), (10, 284), (6, 8)]
    (codeMat 461) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane468GenSource0213 :
    QuotientRankAtLeast (spanCodes [257, 128, 66, 34, 16, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 97), (128, 130), (66, 406), (34, 151), (16, 2), (10, 150), (6, 511)]
    (codeMat 426) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane468GenSource0214 :
    QuotientRankAtLeast (spanCodes [260, 128, 64, 36, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 1), (128, 384), (64, 128), (36, 8), (20, 503), (10, 276), (1, 130)]
    (codeMat 285) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane468GenSource0215 :
    QuotientRankAtLeast (spanCodes [260, 130, 66, 38, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 384), (130, 256), (66, 104), (38, 406), (22, 276), (10, 97), (1, 8)]
    (codeMat 335) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane468GenSource0216 :
    QuotientRankAtLeast (spanCodes [256, 144, 80, 48, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (144, 511), (80, 508), (48, 360), (10, 224), (4, 128), (1, 256)]
    (codeMat 92) (codeMat 242) (codeMat 205) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane468GenSource0217 :
    QuotientRankAtLeast (spanCodes [258, 146, 82, 48, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 361), (146, 256), (82, 255), (48, 8), (10, 28), (6, 1), (1, 3)]
    (codeMat 465) (codeMat 397) (codeMat 250) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane468GenSource0218 :
    QuotientRankAtLeast (spanCodes [274, 130, 82, 32, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(274, 21), (130, 511), (82, 28), (32, 360), (10, 224), (6, 128), (1, 256)]
    (codeMat 95) (codeMat 470) (codeMat 213) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane468GenSource0219 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 34, 19, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 488), (128, 384), (65, 360), (34, 503), (19, 414), (10, 373), (6, 8)]
    (codeMat 270) (codeMat 501) (codeMat 494) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
