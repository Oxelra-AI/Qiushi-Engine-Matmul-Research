import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0580 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 33, 19, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 256), (130, 360), (64, 384), (33, 276), (19, 373), (10, 414), (6, 8)]
    (codeMat 271) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0581 :
    QuotientRankAtLeast (spanCodes [258, 131, 64, 34, 17, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 259), (131, 327), (64, 325), (34, 280), (17, 184), (10, 168), (6, 256)]
    (codeMat 93) (codeMat 247) (codeMat 379) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane490GenSource0582 :
    QuotientRankAtLeast (spanCodes [257, 130, 67, 34, 18, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 70), (130, 3), (67, 199), (34, 240), (18, 216), (10, 248), (7, 128)]
    (codeMat 85) (codeMat 379) (codeMat 247) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane490GenSource0583 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 35, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 128), (129, 374), (64, 384), (35, 381), (19, 373), (10, 235), (7, 511)]
    (codeMat 279) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0584 :
    QuotientRankAtLeast (spanCodes [256, 128, 65, 35, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (128, 3), (65, 360), (35, 503), (19, 373), (10, 414), (7, 511)]
    (codeMat 412) (codeMat 87) (codeMat 468) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0585 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 32, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 128), (128, 384), (66, 374), (32, 130), (19, 235), (10, 373), (7, 511)]
    (codeMat 286) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0586 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 32, 17, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 326), (130, 325), (66, 327), (32, 432), (17, 168), (10, 184), (7, 256)]
    (codeMat 92) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane490GenSource0587 :
    QuotientRankAtLeast (spanCodes [257, 130, 67, 33, 18, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 278), (130, 9), (67, 119), (33, 276), (18, 8), (10, 503), (4, 130)]
    (codeMat 478) (codeMat 106) (codeMat 396) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0588 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 33, 18, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 104), (128, 128), (65, 360), (33, 97), (18, 130), (10, 381), (4, 8)]
    (codeMat 271) (codeMat 85) (codeMat 340) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0589 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 35, 19, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (128, 3), (66, 30), (35, 105), (19, 235), (10, 414), (4, 8)]
    (codeMat 396) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
