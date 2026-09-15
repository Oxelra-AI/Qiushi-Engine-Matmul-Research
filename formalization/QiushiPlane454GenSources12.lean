import QiushiPlane454GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane454GenSource0120 :
    QuotientRankAtLeast (spanCodes [256, 66, 34, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 128), (66, 196), (34, 20), (16, 32), (10, 28), (4, 2), (1, 3)]
    (codeMat 273) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane454GenSource0121 :
    QuotientRankAtLeast (spanCodes [256, 129, 96, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (129, 162), (96, 68), (17, 160), (8, 256), (5, 8), (2, 16)]
    (codeMat 142) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane454GenSource0122 :
    QuotientRankAtLeast (spanCodes [288, 161, 96, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(288, 3), (161, 500), (96, 326), (16, 256), (9, 432), (4, 24), (3, 16)]
    (codeMat 142) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane454GenSource0123 :
    QuotientRankAtLeast (spanCodes [260, 133, 65, 33, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 256), (133, 393), (65, 128), (33, 406), (20, 227), (8, 130), (2, 511)]
    (codeMat 351) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane454GenSource0124 :
    QuotientRankAtLeast (spanCodes [261, 129, 68, 36, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 414), (129, 227), (68, 373), (36, 360), (20, 362), (8, 3), (2, 511)]
    (codeMat 482) (codeMat 415) (codeMat 253) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane454GenSource0125 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 32, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 23), (128, 3), (64, 2), (32, 511), (20, 227), (9, 130), (3, 8)]
    (codeMat 460) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane454GenSource0126 :
    QuotientRankAtLeast (spanCodes [261, 133, 64, 32, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 488), (133, 232), (64, 128), (32, 511), (20, 227), (9, 130), (3, 8)]
    (codeMat 271) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane454GenSource0127 :
    QuotientRankAtLeast (spanCodes [260, 132, 65, 33, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 256), (132, 104), (65, 128), (33, 276), (20, 97), (8, 130), (2, 8)]
    (codeMat 335) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane454GenSource0128 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 32, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 2), (129, 68), (64, 1), (32, 16), (20, 160), (8, 8), (2, 256)]
    (codeMat 84) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane454GenSource0129 :
    QuotientRankAtLeast (spanCodes [260, 133, 64, 32, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 130), (133, 227), (64, 8), (32, 2), (20, 149), (8, 1), (2, 511)]
    (codeMat 482) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
