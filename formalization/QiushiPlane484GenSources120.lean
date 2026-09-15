import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiOrbit23FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource1200 :
    QuotientRankAtLeast (spanCodes [256, 132, 64, 36, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (132, 70), (64, 2), (36, 8), (16, 432), (9, 16), (3, 256)]
    (codeMat 92) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane484GenSource1201 :
    QuotientRankAtLeast (spanCodes [260, 133, 69, 36, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 2), (133, 29), (69, 20), (36, 128), (16, 360), (9, 256), (3, 8)]
    (codeMat 205) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1202 :
    QuotientRankAtLeast (spanCodes [261, 132, 69, 36, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 406), (132, 373), (69, 276), (36, 384), (16, 360), (9, 256), (3, 8)]
    (codeMat 207) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1203 :
    QuotientRankAtLeast (spanCodes [288, 129, 64, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(288, 4), (129, 82), (64, 9), (17, 80), (8, 8), (2, 128)]
    (codeMat 86) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane484GenSource1204 :
    QuotientRankAtLeast (spanCodes [261, 132, 65, 33, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 406), (132, 284), (65, 130), (33, 150), (17, 149), (8, 2), (2, 511)]
    (codeMat 482) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1205 :
    QuotientRankAtLeast (spanCodes [261, 133, 64, 33, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(261, 327), (133, 324), (64, 2), (33, 184), (17, 160), (8, 16), (2, 256)]
    (codeMat 84) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane484GenSource1206 :
    QuotientRankAtLeast (spanCodes [260, 132, 64, 33, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 325), (132, 324), (64, 2), (33, 168), (17, 160), (8, 16), (2, 256)]
    (codeMat 84) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane484GenSource1207 :
    QuotientRankAtLeast (spanCodes [261, 128, 69, 33, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 31), (128, 1), (69, 28), (33, 480), (17, 96), (8, 256), (2, 8)]
    (codeMat 140) (codeMat 358) (codeMat 158) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1208 :
    QuotientRankAtLeast (spanCodes [260, 132, 65, 32, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 1), (132, 324), (65, 2), (32, 8), (17, 160), (8, 16), (2, 256)]
    (codeMat 85) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane484GenSource1209 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 32, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 68), (128, 2), (64, 1), (32, 32), (17, 80), (8, 8), (2, 128)]
    (codeMat 84) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
