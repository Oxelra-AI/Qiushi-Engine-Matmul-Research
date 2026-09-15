import QiushiPlane476GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane476GenSource0080 :
    QuotientRankAtLeast (spanCodes [256, 133, 65, 33, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (133, 71), (65, 3), (33, 424), (20, 184), (9, 24), (3, 256)]
    (codeMat 93) (codeMat 415) (codeMat 253) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane476GenSource0081 :
    QuotientRankAtLeast (spanCodes [257, 132, 64, 32, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 278), (132, 245), (64, 130), (32, 384), (21, 96), (8, 128), (2, 360)]
    (codeMat 158) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane476GenSource0082 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 33, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (129, 327), (65, 325), (33, 264), (17, 184), (10, 168), (5, 256)]
    (codeMat 92) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane476GenSource0083 :
    QuotientRankAtLeast (spanCodes [259, 131, 64, 32, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 136), (131, 392), (64, 384), (32, 3), (18, 511), (10, 510), (5, 360)]
    (codeMat 298) (codeMat 254) (codeMat 443) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane476GenSource0084 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 33, 18, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 387), (128, 1), (65, 384), (33, 235), (18, 8), (10, 503), (7, 130)]
    (codeMat 348) (codeMat 334) (codeMat 442) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane476GenSource0085 :
    QuotientRankAtLeast (spanCodes [256, 131, 67, 35, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (131, 29), (67, 30), (35, 138), (19, 373), (10, 414), (7, 8)]
    (codeMat 460) (codeMat 234) (codeMat 461) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane476GenSource0086 :
    QuotientRankAtLeast (spanCodes [257, 129, 65, 33, 18, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 232), (129, 488), (65, 360), (33, 235), (18, 511), (10, 381), (7, 8)]
    (codeMat 270) (codeMat 247) (codeMat 379) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane476GenSource0087 :
    QuotientRankAtLeast (spanCodes [259, 128, 66, 34, 17, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 406), (128, 511), (66, 227), (34, 392), (17, 480), (10, 224), (6, 8)]
    (codeMat 206) (codeMat 443) (codeMat 254) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane476GenSource0088 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 32, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 128), (129, 224), (64, 256), (32, 2), (18, 511), (10, 508), (6, 360)]
    (codeMat 298) (codeMat 242) (codeMat 205) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane476GenSource0089 :
    QuotientRankAtLeast (spanCodes [262, 128, 70, 38, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(262, 327), (128, 2), (70, 324), (38, 184), (18, 16), (10, 416), (1, 256)]
    (codeMat 92) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
