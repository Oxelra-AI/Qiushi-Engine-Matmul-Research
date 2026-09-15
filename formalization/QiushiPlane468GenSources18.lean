import QiushiPlane468GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane468GenSource0180 :
    QuotientRankAtLeast (spanCodes [273, 144, 80, 48, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(273, 254), (144, 511), (80, 381), (48, 8), (9, 360), (4, 384), (3, 128)]
    (codeMat 85) (codeMat 499) (codeMat 382) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane468GenSource0181 :
    QuotientRankAtLeast (spanCodes [272, 145, 80, 49, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 119), (145, 255), (80, 287), (49, 129), (9, 3), (4, 384), (3, 256)]
    (codeMat 107) (codeMat 443) (codeMat 254) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane468GenSource0182 :
    QuotientRankAtLeast (spanCodes [272, 145, 81, 48, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 381), (145, 361), (81, 353), (48, 130), (9, 256), (5, 3), (3, 1)]
    (codeMat 225) (codeMat 486) (codeMat 157) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane468GenSource0183 :
    QuotientRankAtLeast (spanCodes [257, 129, 81, 32, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 257), (129, 387), (81, 29), (32, 8), (9, 360), (5, 256), (3, 384)]
    (codeMat 85) (codeMat 87) (codeMat 468) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane468GenSource0184 :
    QuotientRankAtLeast (spanCodes [257, 129, 80, 33, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 178), (129, 503), (80, 70), (33, 176), (9, 432), (4, 16), (3, 8)]
    (codeMat 142) (codeMat 250) (codeMat 397) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane468GenSource0185 :
    QuotientRankAtLeast (spanCodes [257, 128, 81, 33, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 257), (128, 130), (81, 149), (33, 264), (8, 360), (5, 256), (2, 128)]
    (codeMat 93) (codeMat 85) (codeMat 340) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane468GenSource0186 :
    QuotientRankAtLeast (spanCodes [257, 128, 80, 32, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 20), (128, 8), (80, 96), (32, 128), (8, 256), (4, 2), (2, 1)]
    (codeMat 161) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane468GenSource0187 :
    QuotientRankAtLeast (spanCodes [273, 144, 80, 48, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(273, 156), (144, 8), (80, 352), (48, 128), (8, 256), (4, 3), (2, 1)]
    (codeMat 177) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane468GenSource0188 :
    QuotientRankAtLeast (spanCodes [274, 144, 82, 50, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(274, 404), (144, 256), (82, 252), (50, 20), (10, 28), (6, 2), (1, 3)]
    (codeMat 401) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane468GenSource0189 :
    QuotientRankAtLeast (spanCodes [272, 146, 80, 50, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 126), (146, 511), (80, 252), (50, 392), (10, 224), (4, 384), (1, 256)]
    (codeMat 93) (codeMat 498) (codeMat 206) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
