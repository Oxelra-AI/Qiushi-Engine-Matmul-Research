import QiushiPlane470GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane470GenSource0180 :
    QuotientRankAtLeast (spanCodes [258, 134, 70, 38, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 287), (134, 252), (70, 245), (38, 224), (18, 256), (10, 264), (1, 360)]
    (codeMat 214) (codeMat 485) (codeMat 171) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane470GenSource0181 :
    QuotientRankAtLeast (spanCodes [258, 132, 70, 36, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 150), (132, 148), (70, 509), (36, 384), (18, 256), (10, 264), (1, 360)]
    (codeMat 213) (codeMat 481) (codeMat 185) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane470GenSource0182 :
    QuotientRankAtLeast (spanCodes [258, 132, 66, 32, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 126), (132, 119), (66, 278), (32, 511), (22, 503), (10, 276), (1, 130)]
    (codeMat 478) (codeMat 444) (codeMat 110) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane470GenSource0183 :
    QuotientRankAtLeast (spanCodes [256, 160, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 256), (160, 68), (68, 160), (16, 1), (8, 2), (2, 8), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane470GenSource0184 :
    QuotientRankAtLeast (spanCodes [259, 131, 67, 32, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 22), (131, 21), (67, 23), (32, 384), (18, 360), (10, 488), (5, 8)]
    (codeMat 140) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane470GenSource0185 :
    QuotientRankAtLeast (spanCodes [259, 131, 64, 35, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 257), (131, 385), (64, 384), (35, 105), (18, 511), (10, 503), (6, 130)]
    (codeMat 277) (codeMat 478) (codeMat 445) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane470GenSource0186 :
    QuotientRankAtLeast (spanCodes [259, 130, 65, 34, 16, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 240), (130, 8), (65, 32), (34, 70), (16, 1), (10, 68), (5, 128)]
    (codeMat 106) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane470GenSource0187 :
    QuotientRankAtLeast (spanCodes [259, 131, 67, 33, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 196), (131, 197), (67, 198), (33, 160), (18, 40), (10, 240), (5, 128)]
    (codeMat 92) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane470GenSource0188 :
    QuotientRankAtLeast (spanCodes [259, 130, 67, 32, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 68), (130, 3), (67, 198), (32, 32), (18, 216), (10, 240), (5, 128)]
    (codeMat 85) (codeMat 346) (codeMat 459) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane470GenSource0189 :
    QuotientRankAtLeast (spanCodes [259, 129, 66, 34, 18, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(259, 324), (129, 70), (66, 71), (34, 416), (18, 432), (10, 440), (4, 256)]
    (codeMat 85) (codeMat 473) (codeMat 409) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
