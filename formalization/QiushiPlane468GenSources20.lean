import QiushiPlane468GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane468GenSource0200 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 37, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 148), (129, 151), (64, 2), (37, 276), (20, 414), (9, 130), (3, 511)]
    (codeMat 468) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane468GenSource0201 :
    QuotientRankAtLeast (spanCodes [260, 132, 65, 32, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 1), (132, 324), (65, 3), (32, 8), (21, 160), (8, 24), (2, 256)]
    (codeMat 85) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane468GenSource0202 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 36, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 21), (128, 1), (64, 2), (36, 360), (20, 104), (8, 128), (2, 8)]
    (codeMat 140) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane468GenSource0203 :
    QuotientRankAtLeast (spanCodes [262, 134, 66, 34, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 413), (134, 245), (66, 278), (34, 414), (22, 373), (10, 406), (1, 130)]
    (codeMat 407) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane468GenSource0204 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 36, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 128), (128, 256), (66, 96), (36, 130), (22, 276), (10, 105), (1, 8)]
    (codeMat 271) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane468GenSource0205 :
    QuotientRankAtLeast (spanCodes [258, 130, 65, 35, 16, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 137), (130, 128), (65, 256), (35, 373), (16, 130), (10, 406), (5, 511)]
    (codeMat 351) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane468GenSource0206 :
    QuotientRankAtLeast (spanCodes [258, 131, 64, 34, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 414), (131, 381), (64, 511), (34, 30), (17, 21), (10, 23), (5, 8)]
    (codeMat 395) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane468GenSource0207 :
    QuotientRankAtLeast (spanCodes [258, 129, 66, 32, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 23), (129, 29), (66, 30), (32, 511), (19, 373), (10, 414), (5, 8)]
    (codeMat 397) (codeMat 494) (codeMat 501) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane468GenSource0208 :
    QuotientRankAtLeast (spanCodes [259, 131, 64, 34, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 240), (131, 248), (64, 32), (34, 70), (17, 199), (10, 196), (5, 128)]
    (codeMat 99) (codeMat 498) (codeMat 206) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane468GenSource0209 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 33, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 31), (128, 3), (66, 30), (33, 503), (19, 235), (10, 414), (5, 8)]
    (codeMat 396) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
