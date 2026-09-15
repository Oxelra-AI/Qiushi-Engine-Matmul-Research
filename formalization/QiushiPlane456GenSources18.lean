import QiushiPlane456GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane456GenSource0180 :
    QuotientRankAtLeast (spanCodes [260, 132, 64, 37, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 360), (132, 363), (64, 1), (37, 97), (20, 235), (9, 8), (3, 511)]
    (codeMat 412) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane456GenSource0181 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 33, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 256), (128, 2), (68, 259), (33, 227), (20, 406), (8, 511), (2, 130)]
    (codeMat 348) (codeMat 345) (codeMat 345) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane456GenSource0182 :
    QuotientRankAtLeast (spanCodes [261, 133, 64, 36, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(261, 326), (133, 324), (64, 3), (36, 432), (20, 416), (8, 24), (2, 256)]
    (codeMat 84) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane456GenSource0183 :
    QuotientRankAtLeast (spanCodes [260, 134, 64, 38, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 3), (134, 29), (64, 9), (38, 235), (20, 373), (10, 97), (1, 8)]
    (codeMat 397) (codeMat 167) (codeMat 167) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane456GenSource0184 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 33, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 96), (128, 128), (64, 256), (33, 97), (16, 130), (10, 276), (4, 8)]
    (codeMat 270) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane456GenSource0185 :
    QuotientRankAtLeast (spanCodes [259, 131, 64, 34, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 240), (131, 248), (64, 32), (34, 70), (17, 199), (10, 196), (5, 128)]
    (codeMat 99) (codeMat 498) (codeMat 206) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane456GenSource0186 :
    QuotientRankAtLeast (spanCodes [258, 130, 67, 35, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 11), (130, 2), (67, 21), (35, 227), (18, 130), (10, 381), (6, 8)]
    (codeMat 397) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane456GenSource0187 :
    QuotientRankAtLeast (spanCodes [258, 129, 66, 32, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 31), (129, 20), (66, 22), (32, 511), (17, 276), (10, 406), (5, 8)]
    (codeMat 397) (codeMat 492) (codeMat 115) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane456GenSource0188 :
    QuotientRankAtLeast (spanCodes [258, 131, 64, 34, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 414), (131, 381), (64, 511), (34, 30), (17, 21), (10, 23), (5, 8)]
    (codeMat 395) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane456GenSource0189 :
    QuotientRankAtLeast (spanCodes [256, 131, 66, 34, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 511), (131, 373), (66, 414), (34, 23), (17, 29), (10, 30), (5, 8)]
    (codeMat 395) (codeMat 494) (codeMat 501) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
