import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0570 :
    QuotientRankAtLeast (spanCodes [257, 129, 65, 34, 18, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 327), (129, 326), (65, 325), (34, 440), (18, 432), (10, 424), (7, 256)]
    (codeMat 84) (codeMat 501) (codeMat 494) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0571 :
    QuotientRankAtLeast (spanCodes [256, 128, 65, 35, 18, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 2), (128, 3), (65, 325), (35, 272), (18, 24), (10, 424), (7, 256)]
    (codeMat 92) (codeMat 115) (codeMat 492) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0572 :
    QuotientRankAtLeast (spanCodes [258, 131, 64, 32, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 480), (131, 232), (64, 360), (32, 511), (19, 235), (10, 373), (7, 8)]
    (codeMat 334) (codeMat 375) (codeMat 491) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0573 :
    QuotientRankAtLeast (spanCodes [256, 131, 67, 32, 16, 11, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 1), (131, 196), (67, 199), (32, 8), (16, 32), (11, 248), (7, 128)]
    (codeMat 84) (codeMat 205) (codeMat 242) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane491GenSource0574 :
    QuotientRankAtLeast (spanCodes [257, 130, 67, 33, 16, 11, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 70), (130, 3), (67, 199), (33, 112), (16, 216), (11, 248), (7, 128)]
    (codeMat 93) (codeMat 379) (codeMat 247) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane491GenSource0575 :
    QuotientRankAtLeast (spanCodes [257, 131, 65, 32, 16, 9, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 129), (131, 196), (65, 3), (32, 8), (16, 32), (9, 216), (5, 128)]
    (codeMat 85) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane491GenSource0576 :
    QuotientRankAtLeast (spanCodes [257, 131, 64, 32, 17, 8, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 136), (131, 240), (64, 216), (32, 1), (17, 198), (8, 3), (5, 128)]
    (codeMat 106) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane491GenSource0577 :
    QuotientRankAtLeast (spanCodes [258, 130, 65, 33, 16, 11, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 510), (130, 1), (65, 3), (33, 232), (16, 8), (11, 136), (5, 360)]
    (codeMat 213) (codeMat 299) (codeMat 318) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0578 :
    QuotientRankAtLeast (spanCodes [258, 129, 66, 34, 19, 11, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 29), (129, 22), (66, 20), (34, 373), (19, 406), (11, 276), (5, 8)]
    (codeMat 461) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0579 :
    QuotientRankAtLeast (spanCodes [258, 128, 67, 35, 18, 11, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 276), (128, 130), (67, 381), (35, 28), (18, 2), (11, 21), (5, 8)]
    (codeMat 459) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
