import QiushiPlane472GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane472GenSource0200 :
    QuotientRankAtLeast (spanCodes [256, 130, 67, 34, 16, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 511), (130, 130), (67, 276), (34, 23), (16, 2), (10, 20), (7, 8)]
    (codeMat 458) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0201 :
    QuotientRankAtLeast (spanCodes [256, 128, 65, 34, 19, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (128, 3), (65, 384), (34, 138), (19, 414), (10, 373), (6, 130)]
    (codeMat 348) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0202 :
    QuotientRankAtLeast (spanCodes [259, 130, 64, 33, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(259, 71), (130, 3), (64, 325), (33, 184), (18, 24), (10, 424), (6, 256)]
    (codeMat 93) (codeMat 375) (codeMat 491) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane472GenSource0203 :
    QuotientRankAtLeast (spanCodes [258, 131, 64, 32, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 258), (131, 326), (64, 325), (32, 16), (18, 432), (10, 424), (6, 256)]
    (codeMat 85) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane472GenSource0204 :
    QuotientRankAtLeast (spanCodes [258, 128, 67, 32, 17, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 509), (128, 360), (67, 361), (32, 130), (17, 97), (10, 105), (6, 511)]
    (codeMat 477) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0205 :
    QuotientRankAtLeast (spanCodes [256, 131, 66, 34, 16, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 9), (131, 252), (66, 287), (34, 352), (16, 256), (10, 224), (6, 360)]
    (codeMat 159) (codeMat 205) (codeMat 242) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0206 :
    QuotientRankAtLeast (spanCodes [258, 128, 67, 32, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 126), (128, 9), (67, 139), (32, 384), (18, 8), (10, 136), (5, 360)]
    (codeMat 159) (codeMat 299) (codeMat 318) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0207 :
    QuotientRankAtLeast (spanCodes [258, 131, 64, 32, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 252), (131, 353), (64, 360), (32, 511), (17, 97), (10, 105), (5, 130)]
    (codeMat 478) (codeMat 485) (codeMat 171) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0208 :
    QuotientRankAtLeast (spanCodes [258, 130, 65, 32, 16, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 136), (130, 128), (65, 384), (32, 3), (16, 2), (10, 150), (5, 360)]
    (codeMat 354) (codeMat 124) (codeMat 124) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0209 :
    QuotientRankAtLeast (spanCodes [260, 132, 65, 37, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 256), (132, 265), (65, 128), (37, 406), (21, 414), (9, 130), (3, 511)]
    (codeMat 342) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
