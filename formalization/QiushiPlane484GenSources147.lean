import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiOrbit23FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource1470 :
    QuotientRankAtLeast (spanCodes [256, 132, 65, 33, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (132, 68), (65, 2), (33, 168), (17, 160), (8, 16), (2, 256)]
    (codeMat 85) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane484GenSource1471 :
    QuotientRankAtLeast (spanCodes [257, 133, 65, 33, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 327), (133, 68), (65, 2), (33, 184), (17, 160), (8, 16), (2, 256)]
    (codeMat 85) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane484GenSource1472 :
    QuotientRankAtLeast (spanCodes [256, 128, 96, 17, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (128, 2), (96, 68), (17, 160), (8, 256), (4, 8), (2, 16)]
    (codeMat 140) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane484GenSource1473 :
    QuotientRankAtLeast (spanCodes [289, 129, 64, 17, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(289, 20), (129, 81), (64, 130), (17, 80), (8, 128), (4, 32), (2, 8)]
    (codeMat 142) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1474 :
    QuotientRankAtLeast (spanCodes [257, 193, 32, 17, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 120), (193, 248), (32, 9), (17, 28), (8, 63), (4, 8), (2, 32)]
    (codeMat 267) (codeMat 205) (codeMat 242) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1475 :
    QuotientRankAtLeast (spanCodes [385, 64, 33, 17, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(385, 80), (64, 128), (33, 20), (17, 21), (8, 2), (4, 32), (2, 40)]
    (codeMat 266) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1476 :
    QuotientRankAtLeast (spanCodes [289, 160, 96, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(289, 387), (160, 252), (96, 245), (17, 96), (8, 360), (5, 384), (2, 256)]
    (codeMat 95) (codeMat 229) (codeMat 187) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1477 :
    QuotientRankAtLeast (spanCodes [256, 129, 96, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (129, 162), (96, 68), (17, 160), (8, 256), (5, 8), (2, 16)]
    (codeMat 142) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane484GenSource1478 :
    QuotientRankAtLeast (spanCodes [257, 129, 97, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 487), (129, 162), (97, 228), (17, 160), (8, 256), (5, 24), (2, 16)]
    (codeMat 142) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane484GenSource1479 :
    QuotientRankAtLeast (spanCodes [448, 33, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(448, 4), (33, 90), (17, 82), (8, 9), (5, 130), (2, 128)]
    (codeMat 266) (codeMat 425) (codeMat 249) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

end QiushiMatmul
