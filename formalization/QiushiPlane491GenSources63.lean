import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0630 :
    QuotientRankAtLeast (spanCodes [264, 129, 64, 32, 16, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(264, 68), (129, 160), (64, 256), (32, 1), (16, 2), (4, 8), (2, 16)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0631 :
    QuotientRankAtLeast (spanCodes [265, 136, 72, 41, 25, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(265, 78), (136, 228), (72, 63), (41, 120), (25, 248), (5, 8), (2, 32)]
    (codeMat 143) (codeMat 489) (codeMat 241) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane491GenSource0632 :
    QuotientRankAtLeast (spanCodes [264, 129, 64, 32, 17, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(264, 68), (129, 170), (64, 325), (32, 256), (17, 168), (5, 8), (2, 16)]
    (codeMat 142) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0633 :
    QuotientRankAtLeast (spanCodes [265, 128, 64, 33, 17, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(265, 118), (128, 128), (64, 384), (33, 510), (17, 150), (5, 1), (2, 2)]
    (codeMat 305) (codeMat 380) (codeMat 117) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0634 :
    QuotientRankAtLeast (spanCodes [256, 144, 81, 49, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (144, 3), (81, 484), (49, 416), (8, 256), (5, 8), (2, 24)]
    (codeMat 142) (codeMat 342) (codeMat 215) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0635 :
    QuotientRankAtLeast (spanCodes [288, 161, 64, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(288, 3), (161, 124), (64, 9), (17, 96), (8, 8), (5, 128), (2, 256)]
    (codeMat 86) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0636 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 32, 16, 13, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (128, 3), (68, 71), (32, 8), (16, 24), (13, 440), (3, 256)]
    (codeMat 84) (codeMat 95) (codeMat 244) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0637 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 32, 20, 8, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 20), (128, 3), (64, 2), (32, 256), (20, 224), (8, 128), (3, 8)]
    (codeMat 140) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0638 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 36, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (132, 21), (68, 20), (36, 128), (16, 360), (9, 256), (3, 8)]
    (codeMat 204) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0639 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 32, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 8), (128, 128), (68, 392), (32, 1), (16, 2), (9, 511), (3, 360)]
    (codeMat 298) (codeMat 93) (codeMat 372) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
