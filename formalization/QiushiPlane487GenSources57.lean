import QiushiPlane487GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane487GenSource0570 :
    QuotientRankAtLeast (spanCodes [257, 131, 65, 33, 17, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 104), (131, 224), (65, 256), (33, 97), (17, 227), (10, 284), (4, 8)]
    (codeMat 335) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane487GenSource0571 :
    QuotientRankAtLeast (spanCodes [259, 130, 67, 32, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 68), (130, 3), (67, 198), (32, 32), (18, 216), (10, 240), (5, 128)]
    (codeMat 85) (codeMat 346) (codeMat 459) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane487GenSource0572 :
    QuotientRankAtLeast (spanCodes [259, 130, 65, 34, 16, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 240), (130, 8), (65, 32), (34, 70), (16, 1), (10, 68), (5, 128)]
    (codeMat 106) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane487GenSource0573 :
    QuotientRankAtLeast (spanCodes [259, 131, 64, 34, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 240), (131, 248), (64, 32), (34, 70), (17, 199), (10, 196), (5, 128)]
    (codeMat 99) (codeMat 498) (codeMat 206) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane487GenSource0574 :
    QuotientRankAtLeast (spanCodes [257, 130, 64, 33, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 362), (130, 3), (64, 511), (33, 488), (17, 480), (10, 224), (5, 360)]
    (codeMat 213) (codeMat 123) (codeMat 236) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane487GenSource0575 :
    QuotientRankAtLeast (spanCodes [259, 128, 64, 33, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 100), (128, 63), (64, 54), (33, 160), (17, 120), (10, 112), (5, 128)]
    (codeMat 95) (codeMat 474) (codeMat 395) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane487GenSource0576 :
    QuotientRankAtLeast (spanCodes [256, 132, 65, 37, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (132, 68), (65, 3), (37, 424), (21, 416), (8, 24), (2, 256)]
    (codeMat 85) (codeMat 397) (codeMat 250) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane487GenSource0577 :
    QuotientRankAtLeast (spanCodes [261, 129, 65, 37, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(261, 71), (129, 324), (65, 1), (37, 440), (21, 416), (8, 8), (2, 256)]
    (codeMat 85) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane487GenSource0578 :
    QuotientRankAtLeast (spanCodes [261, 128, 69, 32, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 22), (128, 1), (69, 20), (32, 384), (17, 96), (8, 256), (2, 8)]
    (codeMat 140) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane487GenSource0579 :
    QuotientRankAtLeast (spanCodes [273, 144, 80, 49, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(273, 163), (144, 1), (80, 324), (49, 160), (8, 256), (4, 24), (2, 8)]
    (codeMat 142) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
