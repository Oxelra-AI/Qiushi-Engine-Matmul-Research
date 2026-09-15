import QiushiPlane315GenData
import QiushiCertifiedTransport
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane315GenSource0050 :
    QuotientRankAtLeast (spanCodes [260, 130, 66, 34, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 384), (130, 256), (66, 104), (34, 406), (20, 276), (10, 105), (1, 8)]
    (codeMat 334) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane315GenSource0051 :
    QuotientRankAtLeast (spanCodes [260, 132, 70, 36, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 1), (132, 361), (70, 149), (36, 8), (22, 105), (10, 227), (1, 511)]
    (codeMat 477) (codeMat 205) (codeMat 242) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane315GenSource0052 :
    QuotientRankAtLeast (spanCodes [260, 128, 66, 32, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 128), (128, 360), (66, 96), (32, 130), (22, 381), (10, 105), (1, 8)]
    (codeMat 335) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane315GenSource0053 :
    QuotientRankAtLeast (spanCodes [260, 128, 70, 32, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 130), (128, 9), (70, 245), (32, 128), (18, 8), (10, 264), (1, 360)]
    (codeMat 159) (codeMat 99) (codeMat 172) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane315GenSource0054 :
    QuotientRankAtLeast (spanCodes [258, 160, 96, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 383), (160, 21), (96, 28), (18, 360), (10, 352), (6, 128), (1, 256)]
    (codeMat 86) (codeMat 486) (codeMat 157) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane315GenSource0055 :
    QuotientRankAtLeast (spanCodes [260, 128, 64, 32, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 1), (128, 384), (64, 128), (32, 8), (22, 503), (10, 406), (1, 130)]
    (codeMat 277) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane315GenSource0056 :
    QuotientRankAtLeast (spanCodes [260, 132, 70, 36, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 128), (132, 137), (70, 118), (36, 130), (20, 138), (10, 227), (1, 511)]
    (codeMat 342) (codeMat 123) (codeMat 236) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane315GenSource0057 :
    QuotientRankAtLeast (spanCodes [260, 134, 66, 38, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 511), (134, 284), (66, 97), (38, 480), (18, 256), (10, 104), (1, 8)]
    (codeMat 207) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane315GenSource0058 :
    QuotientRankAtLeast (spanCodes [260, 130, 70, 34, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 3), (130, 1), (70, 509), (34, 136), (18, 8), (10, 264), (1, 360)]
    (codeMat 157) (codeMat 103) (codeMat 188) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane315GenSource0059 :
    QuotientRankAtLeast (spanCodes [258, 130, 82, 34, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 129), (130, 3), (82, 284), (34, 136), (10, 480), (6, 128), (1, 256)]
    (codeMat 93) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
